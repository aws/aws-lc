"""
Gives one release branch its verdict
Checks whether the fix is already there, then whether the branch still needs it
"""

from engine.inspect_fix import (
    any_bug_commit_present,
    buggy_lines_still_present,
    deleted_lines,
    normalize_spaces,
)
from util.config import (
    AFFECTED,
    ALREADY,
    MAINLINE_REF,
    NOT_AFFECTED,
    UNSURE,
    fingerprint_pathspec,
)
from util.git import (
    branch_paths_by_basename,
    get_file_on_branch,
    git_in_repo,
    show_file,
)

import os
from typing import Iterable, Optional, Sequence, Set

# _________ Is It Already Backported _________


def change_fingerprint(commit: str) -> Optional[str]:
    """The commit's contents as a patch-id, ignoring generated files"""
    show = git_in_repo(
        ["show", commit, *fingerprint_pathspec()],
        capture_output=True,  # bytes, the commit may touch binary files
    )
    if show.returncode != 0:
        return None
    pid = git_in_repo(["patch-id", "--stable"], input=show.stdout, capture_output=True)
    if pid.returncode != 0 or not pid.stdout.strip():
        return None
    return pid.stdout.decode("ascii", errors="replace").split()[0]


def branch_fingerprints(ref: str) -> Set[str]:
    """Fingerprints of the commits the branch has that mainline does not"""
    log = git_in_repo(
        [
            "log",
            "-p",
            "--no-merges",
            "--format=%H",
            f"{MAINLINE_REF}..{ref}",
            *fingerprint_pathspec(),
        ],
        capture_output=True,  # bytes, diffs may contain binary content
    )
    if log.returncode != 0:
        return set()
    pid = git_in_repo(["patch-id", "--stable"], input=log.stdout, capture_output=True)
    if pid.returncode != 0:
        return set()
    out = pid.stdout.decode("ascii", errors="replace")
    return {line.split()[0] for line in out.splitlines() if line.split()}


def branch_mentions_cherry_pick(commit: str, ref: str) -> bool:
    """
    True when a commit on the branch names this one in a cherry picked from line
    Catches reshaped backports whose contents no longer match
    """
    full = git_in_repo(
        ["rev-parse", "--verify", "--quiet", f"{commit}^{{commit}}"],
        capture_output=True,
        text=True,
    )
    if full.returncode != 0 or not full.stdout.strip():
        return False
    log = git_in_repo(
        ["log", "--format=%B%x00", f"{MAINLINE_REF}..{ref}"],
        capture_output=True,
        text=True,
        errors="replace",
    )
    if log.returncode != 0:
        return False
    return f"cherry picked from commit {full.stdout.strip()}" in log.stdout


def is_already_patched(commit: str, branch: str) -> bool:
    """
    Is the fix already on this branch?
    Three ways to tell: it is in the branch history, a commit there names it, or
    one there has the same contents under a different SHA
    """
    ref = f"origin/{branch}"

    # Branch forked after the fix landed, so it has it through shared history
    if git_in_repo(["merge-base", "--is-ancestor", commit, ref]).returncode == 0:
        return True
    if branch_mentions_cherry_pick(commit, ref):
        return True

    fingerprint = change_fingerprint(commit)
    return bool(fingerprint) and fingerprint in branch_fingerprints(ref)


# _________ The Verdict _________


def same_named_file_carries_fix(
    fix_sha: str, src_files: Sequence[str], ref: str
) -> bool:
    """
    Last resort: does a file with the same name elsewhere on the branch hold the bug?
    A name alone proves nothing, so the contents have to hold a deleted line
    """
    by_name = branch_paths_by_basename(ref)
    for file in src_files:
        same_named = by_name.get(os.path.basename(file))
        if not same_named:
            continue
        removed = [normalize_spaces(line) for line in deleted_lines(fix_sha, file)]
        if not removed:
            continue
        for path in same_named:
            content = show_file(ref, path)
            if content and any(line in normalize_spaces(content) for line in removed):
                return True
    return False


def classify_branch(
    fix_sha: str, src_files: Sequence[str], bug_commits: Iterable[str], branch: str
) -> str:
    """
    One branch's verdict, the only copy of this decision
    Anything unclear is UNSURE, never NOT_AFFECTED.
    A wrong not affected means a missed security backport
    """
    ref = f"origin/{branch}"

    # Checked first because applying a fix deletes the buggy lines, which would
    # make still_present below False and send these branches to UNSURE
    if is_already_patched(fix_sha, branch):
        return ALREADY

    affected = any_bug_commit_present(bug_commits, ref)
    still_present = buggy_lines_still_present(fix_sha, tuple(src_files), ref)

    if affected and still_present is not False:
        return AFFECTED
    # History missed it, a branch-only commit wrote the bug, but the lines are here
    if not affected and still_present is True:
        return AFFECTED

    # Not clearly affected. Only call it not affected when the code is not even here
    present = any(
        get_file_on_branch(f, ref, commit=fix_sha)[0] is not None for f in src_files
    )
    if not present:
        present = same_named_file_carries_fix(fix_sha, src_files, ref)
    return UNSURE if present else NOT_AFFECTED
