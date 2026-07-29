"""
Repository targeting: the configured AWS-LC checkout and raw git/command runners.

Layer: impact core (``engine`` package). Builds on nothing.
"""

import os
import subprocess

# ---------------------------------------------------------------------------
# 1. Repository targeting
# ---------------------------------------------------------------------------

# Absolute path to the AWS-LC checkout every git command runs against. None means
# "use the process working directory" (used by the replay test harness, which
# chdirs into a sandbox).
REPO_PATH = None


def set_repo_path(path):
    """Point the engine at an AWS-LC checkout; None restores the cwd fallback."""
    global REPO_PATH
    REPO_PATH = os.path.abspath(path) if path else None


def run_in_repo(cmd, **kwargs):
    """Run a command against REPO_PATH (unless an explicit cwd is given).

    Low-level and raw: returns the ``subprocess`` result and does NOT raise on a
    non-zero exit. (Contrast with ``gitutil.run``/``gitutil.git``, the CLI-facing
    wrappers that raise :class:`~common.BackportError` on failure.)
    """
    if REPO_PATH is not None and kwargs.get("cwd") is None:
        kwargs["cwd"] = REPO_PATH
    return subprocess.run(list(cmd), **kwargs)


def git_in_repo(args, **kwargs):
    """Run a git subcommand against REPO_PATH (raw; see :func:`run_in_repo`)."""
    return run_in_repo(["git", *args], **kwargs)
