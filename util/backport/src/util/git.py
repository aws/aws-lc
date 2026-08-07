# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""
Everything that runs a git command
Only imports util.config, so it can never make an import cycle
"""

from util.config import (
    MAINLINE_REF,
    MAX_DIFF_BYTES,
    MAX_FILE_BYTES,
    TOOL_ROOT,
    BackportError,
)

import os
import subprocess
from contextlib import contextmanager
from typing import Dict, Iterator, List, Optional, Sequence, Tuple

# _________ Where We Run _________

# Git runs in the repo this tool lives in (<repo>/util/backport -> <repo>)
# Pinned instead of using the current directory: we pass repo-relative paths like
# `git diff <sha>^ <sha> -- crypto/x.c` and git matches those against the directory
# it runs in. From a subfolder they match nothing and git still exits 0, so we would
# read an empty diff and give a wrong verdict with no error to show for it
REPO_TOP = str(TOOL_ROOT.parent.parent)


@contextmanager
def using_repo(path) -> Iterator[None]:
    """
    Points git at another checkout for the duration of the block
    Only the replay bench uses this, to aim the engine at a throwaway sandbox
    """
    global REPO_TOP
    previous = REPO_TOP
    REPO_TOP = str(path)
    try:
        yield
    finally:
        REPO_TOP = previous


# _________ Command Runners _________


def git_in_repo(args: Sequence[str], **kwargs):
    """
    Runs a git command in the repo and hands back the result
    Never raises, so callers can treat a failure as an answer
    """
    kwargs.setdefault("cwd", REPO_TOP)
    kwargs.setdefault("check", False)
    return subprocess.run(["git", *args], **kwargs)


def run(args: Sequence[str], check: bool = True):
    """
    Runs a command in the repo and captures its output
    Returns the finished process. Raises BackportError when it fails, unlike
    git_in_repo above
    """
    p = subprocess.run(
        list(args), capture_output=True, text=True, cwd=REPO_TOP, check=False
    )
    if check and p.returncode != 0:
        raise BackportError(
            f"command failed: {' '.join(args)}\nstdout: {p.stdout}\nstderr: {p.stderr}"
        )
    return p


def git(*args: str, check: bool = True):
    """
    Runs a git command through run(), so a failure stops the run
    Returns the finished process
    """
    return run(["git", *args], check=check)


# _________ Finding The Fix _________

# commit-tree will not run without a name and email set, so hand it one
BOT_IDENTITY = (
    "-c",
    "user.name=backport-cli",
    "-c",
    "user.email=backport-cli@local",
)


def range_endpoints(spec: str) -> Optional[Tuple[str, str]]:
    """
    Splits a commit range into (base, head), or None when spec is one commit
    A..B gives (A, B)
    A...B gives (merge-base(A, B), B), the work on B since it forked off A
    An empty side means HEAD
    """
    for sep in ("...", ".."):
        if sep in spec:
            left, right = spec.split(sep, 1)
            left, right = (left or "HEAD"), (right or "HEAD")
            if sep == "...":
                base = git("merge-base", left, right).stdout.strip()
                if not base:
                    raise BackportError(f"no merge base for range '{spec}'.")
                return base, right
            return left, right
    return None


def _rev(ref: str) -> str:
    """
    Turns a ref into a commit SHA, or raises so the user sees the bad name
    """
    r = git("rev-parse", "--verify", f"{ref}^{{commit}}", check=False)
    if r.returncode != 0:
        raise BackportError(f"'{ref}' is not a commit in this checkout.")
    return r.stdout.strip()


def resolve_fix_commit(args) -> Tuple[str, str]:
    """
    Works out which commits to analyze, as (sha, base)

      --commit <ref>       that commit, base is its parent
      --commit A..B/A...B  everything from A to B
      nothing              your branch's commits since it left the mainline

    Nothing is checked out. Several commits get squashed into one commit object with
    commit-tree, so a fix spread over commits is read as its net change
    """
    spec = getattr(args, "commit", None) or f"{MAINLINE_REF}...HEAD"
    endpoints = range_endpoints(spec)
    if endpoints is None:
        fix_sha = _rev(spec)
        return fix_sha, f"{fix_sha}^"

    base_sha, head_sha = _rev(endpoints[0]), _rev(endpoints[1])
    count = int(
        git("rev-list", "--count", f"{base_sha}..{head_sha}").stdout.strip() or 0
    )
    if count == 0:
        raise BackportError(
            f"no commits in '{spec}' -- nothing to analyze.\n"
            "  Commit your fix, or name it with --commit <ref>."
        )
    if count == 1:
        return head_sha, base_sha

    tree = git("rev-parse", f"{head_sha}^{{tree}}").stdout.strip()
    subject = git("log", "-1", "--format=%s", head_sha).stdout.strip()
    squashed = git(
        *BOT_IDENTITY,
        "commit-tree",
        tree,
        "-p",
        base_sha,
        "-m",
        f"[net change of {count} commits] {subject}",
    ).stdout.strip()
    return squashed, base_sha


# _________ Reading What Changed _________


def changed_files_with_status(commit: str) -> Tuple[List[str], List[str]]:
    """
    Files the commit touches, as (all files, traceable files)
    Traceable leaves out files the fix added, since a new file has no history to blame
    Raises when git fails or the commit changes nothing, because an empty list would
    otherwise clear every branch without looking at a single line of code

    Reads `git diff-tree --name-status`, one line per file:
        M     crypto/aead.c              modified
        A     tls/new_feature.c          added
        R100  old.c    new.c             renamed, new path last
    """
    result = git_in_repo(
        ["diff-tree", "--no-commit-id", "--name-status", "-r", commit],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        raise BackportError(
            f"could not read the files '{commit}' changes: {result.stderr.strip()}"
        )
    output = result.stdout

    changed_files: List[str] = []
    traceable_files: List[str] = []
    for line in output.splitlines():
        if not line.strip():
            continue
        columns = line.split("\t")
        status, path = columns[0], columns[-1]  # new path is the last column
        changed_files.append(path)
        if not status.startswith("A"):  # A means the fix added it
            traceable_files.append(path)
    if not changed_files:
        # A merge commit is the one that reaches here: diff-tree shows nothing for it
        # against its first parent, and still exits 0
        raise BackportError(
            f"'{commit}' changes no files, so there is nothing to analyze.\n"
            "A merge commit reports no changes of its own. Analyze what it brought "
            f"in instead, with --commit {commit}^..{commit}"
        )
    return changed_files, traceable_files


def branch_paths_by_basename(ref: str) -> Dict[str, List[str]]:
    """
    Every path on the branch, grouped by filename
    Finds a file the fix touched that moved somewhere git could not follow
    Keeps whole paths, not just names, since a name alone means little when
    internal.h shows up 52 times
    """
    output = git_in_repo(
        ["ls-tree", "-r", "--name-only", ref],
        capture_output=True,
        text=True,
    ).stdout
    grouped: Dict[str, List[str]] = {}
    for path in output.splitlines():
        path = path.strip()
        if path:
            grouped.setdefault(os.path.basename(path), []).append(path)
    return grouped


# _________ Reading Files Through Renames _________


def get_commit_diff(commit: str) -> str:
    """The whole diff for a commit, cut off at MAX_DIFF_BYTES"""
    result = git_in_repo(
        ["show", "--stat", "-p", commit],
        capture_output=True,
        text=True,
        errors="replace",
    )
    if result.returncode != 0:
        return ""
    return result.stdout[:MAX_DIFF_BYTES]


def show_file(ref: str, path: str) -> Optional[str]:
    """
    Contents of the file at that ref, or None when it is not there
    """
    result = git_in_repo(
        ["show", f"{ref}:{path}"],
        capture_output=True,
        text=True,
        errors="replace",
    )
    if result.returncode != 0:
        return None
    return result.stdout


def historical_paths(commit: str, file_path: str, limit: int = 6) -> List[str]:
    """
    Paths the file has had over time, current name first then older ones
    Lets us find the file on a branch that forked before a rename
    """
    paths = [file_path]
    result = git_in_repo(
        ["log", "--follow", "--name-status", "--format=", commit, "--", file_path],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        return paths
    seen = {file_path}
    for line in result.stdout.splitlines():
        parts = line.split("\t")
        # Renames read as R100, old path, new path
        if parts and parts[0].startswith("R") and len(parts) >= 3:
            old = parts[1].strip()
            if old and old not in seen:
                paths.append(old)
                seen.add(old)
                if len(paths) >= limit:
                    break
    return paths


def clip_to_budget(content: str) -> str:
    """
    Content cut to MAX_FILE_BYTES, with a marker saying what was dropped
    Returns it unchanged when it already fits. The marker is the point: a file cut
    off in silence reads to the model as though the code is simply not there, and
    not there is how a branch gets cleared
    """
    if len(content) <= MAX_FILE_BYTES:
        return content
    dropped = len(content) - MAX_FILE_BYTES
    return content[:MAX_FILE_BYTES] + (
        f"\n\n[cut off here, {dropped} more bytes follow in this file. "
        "Code missing below this point is missing from the excerpt, not from the file]"
    )


def get_file_on_branch(
    file_path: str, branch_ref: str, commit: Optional[str] = None
) -> Tuple[Optional[str], Optional[str]]:
    """
    (contents, path) for the file on that branch, cut off at MAX_FILE_BYTES
    Missing at its current path, walks back through older names when given a commit
    Gives (None, None) when the file is nowhere on the branch
    """
    content = show_file(branch_ref, file_path)
    if content is not None:
        return clip_to_budget(content), file_path
    if commit:
        for older in historical_paths(commit, file_path):
            if older == file_path:
                continue
            content = show_file(branch_ref, older)
            if content is not None:
                return clip_to_budget(content), older
    return None, None
