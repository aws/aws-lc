import os
import platform
from collections.abc import Iterator
from contextlib import contextmanager
from functools import cache
from pathlib import Path

import docker
from pydantic import BaseModel
from strands.sandbox.docker import DockerSandbox

from .git import Git
from .target import IntegrationTarget

_RUNNER_TIMEOUT = 3600
_CONTAINER_AWSLC = Path("/aws-lc")
_CONTAINER_SRC = Path("/autofix-src")


class ReplayResult(BaseModel):
    passed: bool
    report: str


class Sandbox:
    """Give the harness separate methods to set up, run, and check the fix for one failed integration target.

    The constructor clones aws-lc and the downstream repos. agent_container starts the container that the agent's
    tools run in. replay reruns the failed CI jobs with a diff applied.
    """

    def __init__(self, root: Path, target: IntegrationTarget, registry: str):
        """Clone aws-lc and the downstream repos at their failing commits, and set what the agent may edit.

        Raise ValueError if this machine's arch has no failed job, since a replay of no jobs would pass.
        """
        self.jobs = target.on(platform.machine())
        if not self.jobs:
            raise ValueError(f"{target.dir_name} has no failed CI job on {platform.machine()}")

        self.root = root.resolve()
        self.target = target
        self.images = f"{registry}/aws-lc"
        self.docker = docker.from_env()

        self.awslc = Git.clone(target.awslc, self.root / "aws-lc")
        self.src = self.root / "src"
        for repo in target.repos:
            Git.clone(repo, self.src / repo.name)
        self.git_repos = {"aws-lc", *(f"src/{repo.name}" for repo in target.repos)}

        patch_dirs = target.patch_dirs(self.awslc.path)
        for patch_dir in patch_dirs:
            (self.awslc.path / patch_dir).mkdir(exist_ok=True)
        self.editable = [*patch_dirs, target.runner]

    @contextmanager
    def agent_container(self) -> Iterator[DockerSandbox]:
        """Start an idle container for the agent's tools to run in, and remove it on exit.

        Everything is read-only except the editable paths. The container has no network and no Linux capabilities.
        """
        container = self.docker.containers.run(
            f"{self.images}/{self.jobs[0].image}",
            ["sleep", "infinity"],
            working_dir=str(self.root),
            volumes=[
                f"{self.root}:{self.root}:ro",
                *(f"{self.awslc.path / path}:{self.awslc.path / path}:rw" for path in self.editable),
            ],
            network_mode="none",
            user=f"{os.getuid()}:{os.getgid()}",
            cap_drop=["ALL"],
            security_opt=["no-new-privileges"],
            detach=True,
        )
        try:
            yield DockerSandbox(container.name)
        finally:
            container.remove(force=True)

    @cache
    def replay(self, diff: str) -> ReplayResult:
        """Rerun this arch's failed CI jobs on a fresh aws-lc copy with the diff applied and local downstream repos."""
        git_env = Git.config_env({"safe.directory": "*"} | {
            f"url.file://{_CONTAINER_SRC / repo.name}.insteadOf": repo.url for repo in self.target.repos
        })
        copy = self.awslc.copy(self.root)
        copy.apply(diff)
        passed, reports = True, []

        try:
            for env in self.jobs:
                container = self.docker.containers.run(
                    f"{self.images}/{env.image}",
                    ["bash", "-c", self.target.script(env)],
                    working_dir=str(_CONTAINER_AWSLC),
                    volumes=[
                        f"{copy.path}:{_CONTAINER_AWSLC}:rw",
                        *(f"{copy.path / path}:{_CONTAINER_AWSLC / path}:ro" for path in [".git", *self.editable]),
                        f"{self.src}:{_CONTAINER_SRC}:ro",
                    ],
                    network_mode="bridge",
                    environment=env.env_vars | git_env,
                    sysctls={"net.ipv6.conf.all.disable_ipv6": "0"} if env.ipv6 else {},
                    security_opt=["no-new-privileges"],
                    init=True,
                    detach=True,
                )
                try:
                    exit_code = container.wait(timeout=_RUNNER_TIMEOUT)["StatusCode"]
                    passed &= exit_code == 0
                    reports.append(f"{env.arch}/{env.image}: exit {exit_code}\n{container.logs().decode(errors='replace')}")
                finally:
                    container.remove(force=True)
        finally:
            # Delete the copy from the container.
            self.docker.containers.run(
                f"{self.images}/{self.jobs[0].image}",
                ["find", str(_CONTAINER_AWSLC), "-mindepth", "1", "-delete"],
                volumes=[f"{copy.path}:{_CONTAINER_AWSLC}:rw"],
                network_mode="none",
                remove=True,
            )
            copy.path.rmdir()
        return ReplayResult(passed=passed, report="\n\n".join(reports))
