import os
import subprocess
import tempfile
from pathlib import Path
from typing import Self

from pydantic import Field
from pydantic.dataclasses import dataclass

_LOCKED_DOWN_GIT = (
    "-c", "protocol.ext.allow=never",
    "-c", "protocol.fd.allow=never",
    "-c", "credential.helper=",
    "-c", "core.hooksPath=/dev/null",
    "-c", "core.symlinks=false",
    "-c", "safe.directory=*",
)


@dataclass(frozen=True)
class Repo:
    """A repo URL and full commit SHA from integration-failure.txt.

    Downstream tests can rewrite that file, so only https URLs, full SHAs, and plain folder names pass.
    """

    url: str = Field(pattern=r"^https://\S+/[A-Za-z0-9_-][A-Za-z0-9._-]*$")
    sha: str = Field(pattern=r"^[0-9a-f]{40}$")

    @property
    def name(self) -> str:
        return Path(self.url).name.removesuffix(".git")


class Git:
    """Run git in one folder with no credentials, config files, hooks, prompts, symlinks, or ext/fd protocols."""

    def __init__(self, path: Path):
        self.path = path
        self.env = {
            "PATH": os.environ["PATH"],
            "HOME": os.devnull,
            "GIT_TERMINAL_PROMPT": "0",
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_GLOBAL": os.devnull,
        }

    def run(self, *args: str, input: str = "") -> str:
        return subprocess.check_output(
            ["git", *_LOCKED_DOWN_GIT, "-C", str(self.path), *args],
            env=self.env,
            input=input,
            text=True,
        )

    @staticmethod
    def config_env(config: dict[str, str]) -> dict[str, str]:
        """Return git settings as GIT_CONFIG_* env vars, so git commands in the replay container use them."""
        env = {"GIT_CONFIG_COUNT": str(len(config))}
        for index, (key, value) in enumerate(config.items()):
            env |= {f"GIT_CONFIG_KEY_{index}": key, f"GIT_CONFIG_VALUE_{index}": value}
        return env

    @staticmethod
    def changed_paths(diff: str) -> list[Path]:
        numstat = Git(Path("/")).run("apply", "--numstat", "-", input=diff)
        return [Path(line.split("\t")[-1]) for line in numstat.splitlines()]

    @classmethod
    def clone(cls, repo: Repo, path: Path) -> Self:
        """Clone the repo at its SHA and point every branch at that SHA.

        A runner that clones this repo gets the commit that failed in CI in case GitHub added a new commit.
        """
        path.mkdir(parents=True)
        git = cls(path)
        git.run("init", "-q")
        git.run("fetch", "-q", "--no-tags", "--depth", "500", repo.url, repo.sha)
        git.run("checkout", "-q", "FETCH_HEAD")

        history = set(git.run("rev-list", "HEAD").split())
        remote = git.run("ls-remote", "--heads", "--tags", repo.url)
        refs = {
            name.removesuffix("^{}"): sha
            for sha, name in (line.split("\t") for line in remote.splitlines())
        }

        updates = [
            f"update {name} {repo.sha if name.startswith('refs/heads/') else sha}\n"
            for name, sha in refs.items()
            if name.startswith("refs/heads/") or sha in history
        ]
        git.run("update-ref", "--stdin", input="".join(updates))
        return git

    def copy(self, parent: Path) -> Self:
        """Copy HEAD into a new folder under parent, so a CI replay cannot dirty this checkout."""
        copy = type(self)(Path(tempfile.mkdtemp(prefix="replay-", dir=parent)))
        self.run("clone", "-q", "--no-checkout", str(self.path), str(copy.path))
        copy.run("checkout", "-q", self.run("rev-parse", "HEAD").strip())
        return copy

    def diff(self, paths: list[Path]) -> str:
        """Return the working-tree diff of the paths, including new files."""
        self.run("add", "--intent-to-add", "--", *map(str, paths))
        return self.run("diff", "--no-renames", "--", *map(str, paths))

    def apply(self, diff: str) -> None:
        if diff:
            self.run("apply", "-", input=diff)
