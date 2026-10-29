import logging
import shlex
from pathlib import Path
from typing import Annotated, Literal, Self

from pydantic import BaseModel, Field

from .git import Repo

# Allow only characters that cannot break out of a shell word, because downstream tests can rewrite the report.
ShellSafe = Annotated[str, Field(pattern=r"^[A-Za-z0-9._:-]*$")]


class Environment(BaseModel, frozen=True):
    """The container setup of one failed CI job, read from its failure report.

    The replay needs it to rerun the job with the same image, compiler, user, and environment variables as CI.
    """
    image: ShellSafe
    compiler: ShellSafe
    arch: Literal["x86_64", "aarch64"]
    size: ShellSafe
    job_id: int
    user: ShellSafe = ""
    ipv6: bool = False
    env_vars: dict[str, str]


class IntegrationTarget(BaseModel):
    """One integration and version to fix, with every CI job that failed for it.

    The workflow passes it as JSON in TARGET to the reason and review jobs. It finds the runner script and its
    patch folders, and it builds the script that reruns each failed job.
    """
    name: str = Field(pattern=r"^[a-z0-9_]+$")
    version: str = Field(pattern=r"^[A-Za-z0-9._/-]*$")
    awslc: Repo
    repos: list[Repo]
    environments: list[Environment]

    @classmethod
    def from_reports(cls, reports: Path, awslc: Repo) -> list[Self]:
        """Read every failure report in a folder and return one target per integration and version.

        Each failed CI job writes its own report. When python 3.13 fails on both x86_64 and aarch64, the two reports
        become one target. Reports that do not parse are logged and skipped.
        """
        targets = {}
        for report in sorted(path.read_text() for path in reports.rglob("integration-failure.txt")):
            try:
                head, *lines = report.splitlines()
                name, version = head.split("\t")

                repos = [Repo(*line.removeprefix("commit=").split()) for line in lines if line.startswith("commit=")]
                env = Environment.model_validate_json(lines[-1].removeprefix("job="))

                target = targets.setdefault(
                    (name, version),
                    cls(name=name, version=version, awslc=awslc, repos=repos, environments=[]),
                )
                target.environments.append(env)
            except (ValueError, IndexError) as error:
                logging.warning("skipping a bad integration-failure.txt: %s", error)
        return list(targets.values())

    @property
    def dir_name(self) -> str:
        return f"{self.name}-{self.version}".rstrip("-").replace("/", "-")

    @property
    def runner(self) -> Path:
        return Path("tests/ci/integration") / f"run_{self.name}_integration.sh"

    def patch_dirs(self, awslc: Path) -> list[Path]:
        """Return the target's own patch folder and every other patch folder its runner script names."""
        runner_text = (awslc / self.runner).read_text()
        named = {folder.name for folder in (awslc / self.runner.parent).glob("*_patch") if folder.name in runner_text}
        return sorted(self.runner.parent / name for name in named | {f"{self.name}_patch"})

    def on(self, arch: str) -> list[Environment]:
        return [env for env in self.environments if env.arch == arch]

    def script(self, env: Environment) -> str:
        """Return the bash script that runs the runner the way the failed CI job did, with the aws CLI stubbed out."""
        script = "; ".join([
            "aws() { :; }",
            "export -f aws",
            f"source /opt/compiler-env/setup-{env.compiler}.sh",
            f"./{self.runner} {shlex.quote(self.version)}",
        ])
        if not env.user:
            return script

        home = f"/home/{env.user}"
        script = f'export HOME={home} PATH="$CONTAINER_PATH"; {script}'
        return "; ".join([
            f"mkdir -p {home}",
            f"chown -R {env.user} {home} . 2>/dev/null",
            "git config --system --add safe.directory '*'",
            'export CONTAINER_PATH="$PATH"',
            f"su -p {env.user} -c {shlex.quote(script)}",
        ])
