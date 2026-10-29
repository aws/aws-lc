import json
import os
import re
import shlex
import threading
import unicodedata
from datetime import UTC, datetime
from pathlib import Path
from typing import Any, Self

from pydantic import BaseModel
from strands import ModelRetryStrategy, ToolContext, tool
from strands.agent import AgentResult
from strands.tools.executors import SequentialToolExecutor
from strands.types.agent import Limits
from strands.vended_tools.shell.types import ShellOutput
from strands_harness import create_harness

from .git import Git, Repo
from .sandbox import Sandbox, ReplayResult
from .target import IntegrationTarget

_MODEL = f"bedrock/{json.loads((Path(__file__).parents[4] / '.github/workflows/ai-config.json').read_text())['opus']}"
_LIMITS = Limits(turns=150, total_tokens=6_000_000)
_TIMEOUT = 45 * 60
_REASON_TIMEOUT = 60 * 60
_PROMPTS = Path(__file__).parent / "prompts"
_READ_LOG_MAX_LINES = 2000
_COMMAND_TIMEOUT = 120
_READ_ONLY_PROGRAMS = {"grep", "ls", "cat", "head", "tail", "wc", "diff"}
_GIT_READ_COMMANDS = {"log", "show", "diff", "blame", "grep", "ls-files"}
_GIT_BLOCKED_OPTIONS = ("--open-files-in-pager", "--output", "--ext-diff")
_SED_PRINT_RANGE = re.compile(r"\d+,\d+[pl]")
_RUN_COMMAND_DESCRIPTION = (
    "Run one read-only command in the sandbox and return its output, error, and exit code.\n\n"
    "argv is a list of arguments, not a shell string, so pipes, redirects, globs, and variables do not work.\n"
    f"Allowed: {', '.join(sorted(_READ_ONLY_PROGRAMS))}; sed -n 'A,Bp' or 'A,Bl'; patch --dry-run; "
    f"git -C aws-lc|src/<repo> {'|'.join(sorted(_GIT_READ_COMMANDS))}."
)
_LICENSE = ("By submitting this pull request, I confirm that my contribution is made under the terms of the "
            "Apache 2.0 license and the ISC license.")
_SECRET_PATTERNS = (
    re.compile(r"\b(?:AKIA|ASIA)[0-9A-Z]{16}\b"),
    re.compile(r"aws_secret_access_key\s*=\s*\S+", re.I),
    re.compile(r"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----"),
    re.compile(r"\bgh[pousr]_[A-Za-z0-9]{36,}\b"),
    re.compile(r"\b(?:Bearer|Authorization:)\s+[A-Za-z0-9._\-]{20,}"),
    re.compile(r"https?://\S*\.(?:amazon|a2z|aws\.dev|corp)\b\S*"),
)
_INVISIBLE_CATEGORIES = {"Cc", "Cf", "Cn", "Zl", "Zp"}


def _runs_or_writes(arg: str) -> bool:
    """Return whether a git option can start a program or write a file.

    run_command uses this to keep the agent's git commands read-only. For example, "git grep -O sh" would run sh.
    Abbreviations and bundled short flags count, so "--outp=x" and "-iOsh" match but "--oneline" does not.
    """
    name = arg.split("=", 1)[0]
    if name.startswith("--"):
        return len(name) > 2 and any(option.startswith(name) for option in _GIT_BLOCKED_OPTIONS)
    return name.startswith("-") and "O" in name


class ReviewVerdict(BaseModel):
    """The reviewer agent's verdict, which Strands makes it return as structured output.

    safe decides if a PR opens.
    """
    safe: bool


class _BedrockRetry(ModelRetryStrategy):
    """Strands' way to choose which model errors to retry. Retries throttling and brief Bedrock outages"""
    def is_retryable(self, exception: Exception) -> bool:
        transient = ("serviceUnavailableException", "internalServerException", "modelStreamErrorException")
        return super().is_retryable(exception) or any(code in str(exception) for code in transient)


class Harness:
    """Run the autofix agents for one failed integration target."""
    def __init__(self, work_dir: Path, target: IntegrationTarget):
        self.work_dir = work_dir
        self.target = target
        self.out = work_dir / "out"
        self.logs = {log.name: log for log in sorted((self.out / "logs").glob("*.log"))}

    @classmethod
    def from_env(cls) -> Self:
        return cls(Path(os.environ["WORK_DIR"]), IntegrationTarget.model_validate_json(os.environ["TARGET"]))

    @staticmethod
    def recognize(reports: Path, awslc: Repo) -> list[dict]:
        """Return the GitHub Actions matrix of targets to fix, with one entry per integration and version.

        A target that failed on both x86_64 and aarch64 runs its reason job on x86_64.
        """
        matrix = []
        for target in IntegrationTarget.from_reports(reports, awslc):
            env = (target.on("x86_64") or target.environments)[0]
            matrix.append({
                "name": target.dir_name,
                "arch": env.arch,
                "size": env.size,
                "target": target.model_dump(mode="json"),
            })
        return matrix

    @staticmethod
    def _run_agent(instructions: str, message: str, timeout: int, **options: Any) -> AgentResult:
        agent = create_harness(**{
            "model": _MODEL,
            "instructions": instructions,
            "builtin_tools": [],
            "builtin_plugins": [],
            "session": False,
            "memory": False,
            "skills": False,
            "background_tasks": False,
            "tool_executor": SequentialToolExecutor(),
            "retry_strategy": _BedrockRetry(),
        } | options)
        timer = threading.Timer(timeout, agent.cancel)
        timer.start()
        try:
            return agent(message, limits=_LIMITS)
        finally:
            timer.cancel()

    def reason(self, registry: str) -> ReplayResult:
        """Run an agent that fixes the runner script and .patch files in a container with no network.

        Tools: read, write, edit, run_command (read-only commands), and run_integration.
        run_integration reruns each failed CI job in its original container image with the agent's changes.
        """
        self.sandbox = Sandbox(self.work_dir, self.target, registry)

        instructions = (_PROMPTS / "agent.md").read_text().format(
            name=self.target.name,
            version=self.target.version,
            root=self.sandbox.root,
            repos=", ".join(f"`src/{repo.name}` ({repo.url} at {repo.sha})" for repo in self.target.repos),
            editable=", ".join(f"`aws-lc/{path}`" for path in self.sandbox.editable),
        )

        with self.sandbox.agent_container() as container:
            final_message = self._run_agent(
                instructions,
                "Start by reading the logs.",
                _REASON_TIMEOUT,
                sandbox=container,
                tools=[self.run_integration, self.run_command],
                builtin_tools=["read", "write", "edit"],
            )

        if final_message.stop_reason != "end_turn":
            raise RuntimeError(f"{self.target.dir_name}: the agent stopped early ({final_message.stop_reason})")

        diff = self.sandbox.awslc.diff(self.sandbox.editable)
        (self.out / "changes.diff").write_text(diff)
        (self.out / "description.md").write_text(str(final_message))

        result = self.sandbox.replay(diff) if diff else ReplayResult(passed=False, report="The agent changed nothing.")
        (self.out / "replay.json").write_text(result.model_dump_json(indent=2))
        return result

    @tool
    def read_log(self, name: str, start_line: int) -> str:
        """Return up to 2000 lines of one failed CI job log, from start_line on.

        Call this tool more than once to read a long log in parts. A whole log can overflow the context.
        For example, two postgres job logs were 1.77M tokens, which is over the 1M limit.

        Args:
            name: A log file name from the <logs> list, e.g. "12345.log".
            start_line: The first line to return, counting from 1.
        """
        lines = self.logs[name].read_text().splitlines()
        start = max(start_line, 1) - 1
        return "\n".join(lines[start:start + _READ_LOG_MAX_LINES])

    @tool
    def run_integration(self) -> ReplayResult:
        """Replay every failed CI job on a fresh copy of aws-lc with the current changes.

        Return whether all jobs passed, plus each job's exit code and logs.
        """
        return self.sandbox.replay(self.sandbox.awslc.diff(self.sandbox.editable))

    @tool(context=True, description=_RUN_COMMAND_DESCRIPTION)
    async def run_command(self, argv: list[str], tool_context: ToolContext) -> ShellOutput:
        """Run one allowed read-only command in the container.

        Raise ValueError if the command is not allowed.
        """
        self._check(argv)
        result = await tool_context.agent.sandbox.execute(shlex.join(argv), timeout=_COMMAND_TIMEOUT)
        return {"output": result.stdout, "error": result.stderr, "exit_code": result.exit_code}

    def _check(self, argv: list[str]) -> None:
        match argv:
            case [program, *_] if program in _READ_ONLY_PROGRAMS:
                return
            case ["git", "-C", repo, command, *args] if (
                    repo in self.sandbox.git_repos and command in _GIT_READ_COMMANDS
                    and not any(map(_runs_or_writes, args))):
                return
            case ["patch", *args] if "--dry-run" in args:
                return
            case ["sed", "-n", script, _] if _SED_PRINT_RANGE.fullmatch(script):
                return
        raise ValueError(f"not allowed: {shlex.join(argv)}")

    def review(self) -> ReviewVerdict:
        """Run a new agent that judges the fix, if the fix passes run_integration and the fixed rules.

        The agent checks for unsafe changes and uses read_log to check that the fix matches the failed CI job logs.
        pr.md is written only for a safe fix.
        """
        replay = ReplayResult.model_validate_json((self.out / "replay.json").read_text())
        diff, description = (self.out / "changes.diff").read_text(), (self.out / "description.md").read_text()

        if not (replay.passed and self._follows_rules(diff, description)):
            verdict = ReviewVerdict(safe=False)
        else:
            logs = "\n".join(f"- `{log.name}`: {len(log.read_text().splitlines())} lines"
                             for log in self.logs.values())
            message = (f"<logs>\n{logs}\n</logs>\n\n<diff>\n{diff}\n</diff>\n\n"
                       f"<description>\n{description}\n</description>")

            verdict = self._run_agent(
                (_PROMPTS / "review.md").read_text(),
                message,
                _TIMEOUT,
                structured_output_model=ReviewVerdict,
                tools=[self.read_log],
            ).structured_output

        (self.out / "review.json").write_text(verdict.model_dump_json(indent=2))
        if verdict.safe:
            run_url = "{GITHUB_SERVER_URL}/{GITHUB_REPOSITORY}/actions/runs/{GITHUB_RUN_ID}".format_map(os.environ)
            bot = f"Generated by autofix with `{_MODEL}` at {datetime.now(UTC):%Y-%m-%d %H:%M} UTC in {run_url}."
            (self.out / "pr.md").write_text(f"{description.strip()}\n\n{bot}\n\n{_LICENSE}\n")
        return verdict

    def _follows_rules(self, diff: str, description: str) -> bool:
        """Return whether the diff edits only the runner and its .patch files, with no secrets or hidden text."""
        if not diff:
            return False
        runner = self.target.runner
        added = [line[1:] for line in diff.splitlines() if line.startswith("+")]
        text = "\n".join([*added, description])
        return (
            all(path == runner or (path.suffix == ".patch" and path.is_relative_to(runner.parent))
                for path in Git.changed_paths(diff))
            and not any(pattern.search(text) for pattern in _SECRET_PATTERNS)
            and not any(unicodedata.category(char) in _INVISIBLE_CATEGORIES and char not in "\t\n\r" for char in text)
        )
