# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""
Everything that runs a git command
Only imports util.config, so it can never make an import cycle
"""

from util.config import (
    MAX_DIFF_BYTES,
    MAX_FILE_BYTES,
    RELEASE_REMOTE,
    TOOL_ROOT,
    BackportError,
)

import os
import re
import subprocess
from contextlib import contextmanager
from functools import lru_cache
from typing import Dict, Iterator, List, Optional, Sequence, Tuple

# --- Where We Run ---

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
    Every cache in this module keys on refs or paths that belong to one checkout, so
    they are dropped on the way in and on the way out. A sandbox has its own remotes,
    and a stale release_remote would send every lookup at a ref that is not there
    """
    global REPO_TOP
    previous = REPO_TOP
    REPO_TOP = str(path)
    _clear_repo_caches()
    try:
        yield
    finally:
        REPO_TOP = previous
        _clear_repo_caches()


def _clear_repo_caches() -> None:
    """Drops every cache in this module that is only valid for one checkout"""
    release_remote.cache_clear()
    file_on_branch.cache_clear()
    historical_paths.cache_clear()


# --- Which Remote Holds The Release Branches ---


@lru_cache(maxsize=1)
def release_remote() -> str:
    """
    The remote to read release branches from
    Returns BACKPORT_REMOTE when set, else the remote pointing at aws/aws-lc, else
    origin. Locally origin is usually a fork, which may be missing the release
    branches or stale on them, so reading them from the remote that owns them is safer.
    In CI there is only origin and it already is aws/aws-lc, so this picks it either way
    """
    if RELEASE_REMOTE:
        return RELEASE_REMOTE
    listed = git("remote", "-v", check=False)
    if listed.returncode == 0:
        for line in listed.stdout.splitlines():
            parts = line.split()
            if len(parts) >= 2 and re.search(
                r"github\.com[:/]+aws/aws-lc(\.git)?$", parts[1]
            ):
                return parts[0]
    return "origin"


def branch_ref(branch: str) -> str:
    """The remote-tracking ref for a release branch, e.g. upstream/fips-2024-09-27"""
    return f"{release_remote()}/{branch}"


def mainline_ref() -> str:
    """The ref a release branch's own commits are measured against"""
    return f"{release_remote()}/main"


# --- Command Runners ---


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


# --- Finding The Fix ---

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
    spec = getattr(args, "commit", None) or f"{mainline_ref()}...HEAD"
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


# --- Reading What Changed ---


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


# --- Reading Files Through Renames ---


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


@lru_cache(maxsize=None)
def historical_paths(commit: str, file_path: str, limit: int = 6) -> List[str]:
    """
    Paths the file has had over time, current name first then older ones
    Lets us find the file on a branch that forked before a rename. Cached because
    every branch asks the same question about the same file
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


@lru_cache(maxsize=None)
def file_on_branch(ref: str, path: str) -> bool:
    """Whether the branch has that path at all, without reading the file"""
    return git("cat-file", "-e", f"{ref}:{path}", check=False).returncode == 0


def resolve_on_branch(
    file_path: str, branch_ref: str, commit: Optional[str] = None
) -> Optional[str]:
    """
    The path this file lives at on the branch, following renames
    Returns None when it is nowhere on the branch. Only asks git whether the path
    exists, so a caller that just needs to know that never loads the contents
    """
    if file_on_branch(branch_ref, file_path):
        return file_path
    if commit:
        for older in historical_paths(commit, file_path):
            if older != file_path and file_on_branch(branch_ref, older):
                return older
    return None


# --- Backporting ---

# Cherry-picks happen in a worktree under here, never in the tree you are sitting in
WORKTREE_ROOT = TOOL_ROOT / ".backport-worktrees"


def commit_exists(sha: str) -> bool:
    """True when this checkout still has that commit"""
    return git("cat-file", "-e", f"{sha}^{{commit}}", check=False).returncode == 0


def branch_exists(name: str) -> bool:
    """True when that local branch already exists"""
    ref = f"refs/heads/{name}"
    return git("show-ref", "--verify", "--quiet", ref, check=False).returncode == 0


def add_worktree(path, branch: str, start_point: str) -> None:
    """
    Checks start_point out at path on a new branch
    A worktree is used so apply never moves the branch you have checked out, and an
    unfinished cherry-pick can never strand your own working tree mid-merge
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    git("worktree", "add", "-q", "-b", branch, str(path), start_point)


def remove_worktree(path) -> None:
    """Drops the worktree but keeps the branch it built"""
    git("worktree", "remove", "--force", str(path), check=False)


def cherry_pick(path, sha: str) -> Tuple[bool, List[str]]:
    """
    Cherry-picks sha in the worktree at path
    Returns (applied, conflicted files). The user's own name lands on the commit
    because git is left to read their config, so the result is theirs to push

    -x is what writes the "cherry picked from commit" line into the message, which is
    one of the three signals analyze uses to spot a branch that already has the fix.
    Without it the tool could not recognise its own backports on the next run
    """
    picked = git("-C", str(path), "cherry-pick", "-x", sha, check=False)
    if picked.returncode == 0:
        return True, []
    unmerged = git(
        "-C", str(path), "diff", "--name-only", "--diff-filter=U", check=False
    )
    return False, [f for f in unmerged.stdout.splitlines() if f.strip()]


def cherry_pick_was_empty(path) -> bool:
    """
    True when the cherry-pick stopped because the change is already there
    git calls this an empty commit, which means the branch did not need the fix
    """
    state = git("-C", str(path), "status", "--porcelain", check=False)
    return not state.stdout.strip()


def abort_cherry_pick(path) -> None:
    """Backs a stopped cherry-pick out, leaving the worktree on its branch"""
    git("-C", str(path), "cherry-pick", "--abort", check=False)


def cherry_pick_in_progress(path) -> bool:
    """
    True while a cherry-pick in that worktree is still stopped part way
    This is what tells a resolved conflict from an open one, so publish can pick up a
    branch the user finished by hand without apply having to run again
    """
    head = git(
        "-C", str(path), "rev-parse", "-q", "--verify", "CHERRY_PICK_HEAD", check=False
    )
    return head.returncode == 0


def commits_ahead(base_ref: str, branch: str) -> int:
    """How many commits branch has that base_ref does not. 0 when git cannot tell"""
    counted = git("rev-list", "--count", f"{base_ref}..{branch}", check=False)
    if counted.returncode != 0:
        return 0
    return int(counted.stdout.strip() or 0)


def commit_subject(commit: str) -> str:
    """The one-line subject of a commit, or an empty string when git cannot read it"""
    subject = git("log", "-1", "--format=%s", commit, check=False)
    return subject.stdout.strip() if subject.returncode == 0 else ""
