# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""
Reads the fix: which lines it deletes and which commits wrote them
Nothing here looks at a release branch except to check the lines are still on it
"""

from util.config import BackportError, is_test_or_generated_file
from util.git import git_in_repo, show_file

import re
import sys
from functools import lru_cache
from typing import Iterable, List, Optional, Sequence, Set, Tuple

# _________ Which Lines To Look For _________

C_EXTENSIONS = (".c", ".cc", ".cpp", ".cxx", ".h", ".hpp", ".hh", ".hxx")


def normalize_spaces(s: str) -> str:
    """
    Collapses runs of whitespace so a reformatted line still matches
    Returns the collapsed line
    """
    return re.sub(r"\s+", " ", s).strip()


def is_c_file(file: Optional[str]) -> bool:
    """True for C and C++ files, where # is a directive and not a comment"""
    return file is not None and file.lower().endswith(C_EXTENSIONS)


def is_comment_or_blank(s: str, file: Optional[str] = None) -> bool:
    """True for lines that say nothing about the bug: comments, blanks, punctuation"""
    s = s.strip()
    if not s:
        return True
    if s.startswith(("//", "/*", "*/", "*")):
        return True
    if s.startswith("#") and not is_c_file(file):
        return True
    return set(s) <= set("{}();,: \t")


def is_too_common_to_match(s: str) -> bool:
    """
    True for real code that appears everywhere, like a bare return or an include
    Skipping these only weakens a match, so it can never cause a missed backport
    """
    s = s.strip()
    if re.match(r"^(return|break|continue|goto)\b[^;{}]*;?$", s):
        return True
    if s.startswith("#include"):
        return True
    # Nothing left but a string literal is not distinctive enough
    without_strings = re.sub(r'"(?:[^"\\]|\\.)*"|\'(?:[^\'\\]|\\.)*\'', "", s)
    return len(re.sub(r"\W", "", without_strings)) < 6


def only_source_files(files: Sequence[str]) -> List[str]:
    """
    Drops tests and generated files, since neither is the shipped code
    Keeps everything when the fix touches nothing else
    Returns the files worth analyzing
    """
    return [f for f in files if not is_test_or_generated_file(f)] or list(files)


@lru_cache(maxsize=None)
def deleted_lines(commit: str, file: str) -> List[str]:
    """
    The distinctive lines the commit deletes from the file
    Returns an empty list when the diff fails or nothing distinctive was deleted
    """
    diff = git_in_repo(
        ["diff", f"{commit}^", commit, "--", file], capture_output=True, text=True
    )
    if diff.returncode != 0:
        return []
    removed = []
    for line in diff.stdout.splitlines():
        if not line.startswith("-") or line.startswith("---"):
            continue
        s = line[1:].strip()
        if is_comment_or_blank(s, file) or is_too_common_to_match(s):
            continue
        if len(re.sub(r"\W", "", s)) >= 6:  # enough letters to be distinctive
            removed.append(s)
    return removed


@lru_cache(maxsize=None)
def buggy_lines_still_present(
    commit: str, changed_files: Tuple[str, ...], ref: str
) -> Optional[bool]:
    """
    Are the lines the fix deletes still on the branch?
    True still there, False gone, None the fix deleted nothing to look for
    """
    saw_removed = False
    for file in changed_files:
        # A hit in a test or generated file is not the shipped code
        if is_test_or_generated_file(file):
            continue
        removed = deleted_lines(commit, file)
        if not removed:
            continue
        saw_removed = True
        content = show_file(ref, file)
        if content is None:
            continue
        content = normalize_spaces(content)
        if any(normalize_spaces(line) in content for line in removed):
            return True
    return False if saw_removed else None


# _________ Which Commits Wrote The Bug _________


def blame_lines(file: str, line_start: int, line_end: int, ref: str) -> Optional[str]:
    """
    Oldest commit to touch those lines, from `log -L` or failing that `blame`
    Returns None when neither can name a commit, usually a fix that only added lines
    """
    log = git_in_repo(
        ["log", f"-L{line_start},{line_end}:{file}", "--format=%H", "--reverse", ref],
        capture_output=True,
        text=True,
    )
    if log.returncode == 0:
        # --format=%H prints SHAs on their own line, the rest is diff body
        for line in log.stdout.splitlines():
            if re.fullmatch(r"[0-9a-f]{40}", line.strip()):
                return line.strip()

    # blame is less accurate for the original bug, but handles cases log -L cannot
    blame = git_in_repo(
        ["blame", "-w", "-M", "-C", "-L", f"{line_start},{line_end}", ref, "--", file],
        capture_output=True,
        text=True,
    )
    if blame.returncode != 0:
        # Usually the fix only added lines, so the parent has nothing to blame
        print(
            f"[bug commit] nothing deleted for {file}:{line_start}-{line_end} on "
            f"{ref}, skipping this hunk",
            file=sys.stderr,
        )
        return None
    for line in blame.stdout.splitlines():
        if line:
            return line.split()[0].lstrip("^")
    return None


def find_bug_commits(commit: str, files: Sequence[str]) -> Set[str]:
    """
    The commits that wrote the lines this fix changes
    Hunks that only touch comments are skipped, so a stale comment cannot drag in
    some ancient unrelated commit
    Returns their SHAs, empty when nothing could be blamed
    """
    bug_commits = set()
    for file in files:
        # Blaming a test or generated file would flag branches without the real code
        if is_test_or_generated_file(file):
            continue
        diff = git_in_repo(
            ["diff", "-U0", f"{commit}^", commit, "--", file],
            capture_output=True,
            text=True,
        )
        if diff.returncode != 0:
            raise BackportError(f"git diff failed: {diff.stderr}")

        # Collect each hunk with its changed lines so noise-only ones can be dropped
        hunks = []
        current = None
        for line in diff.stdout.splitlines():
            if line.startswith("@@"):
                current = None
                match = re.match(r"^@@ -(\d+)(?:,(\d+))? ", line)
                if match:
                    start = int(match.group(1))
                    count = int(match.group(2)) if match.group(2) else 1
                    current = (start, count, [])
                    hunks.append(current)
            elif current and line[:1] in ("+", "-") and line[:3] not in ("+++", "---"):
                current[2].append(line[1:])

        for start, count, changed in hunks:
            if changed and all(is_comment_or_blank(c, file) for c in changed):
                continue
            if count == 0:
                # Nothing deleted, so blame the line after the insertion
                first, last = start + 1, start + 1
            else:
                first, last = start, start + count - 1
            sha = blame_lines(file, first, last, f"{commit}^")
            if sha:
                bug_commits.add(sha)
    return bug_commits


def any_bug_commit_present(bug_commits: Iterable[str], ref: str) -> bool:
    """True when any bug commit is on the branch, same SHA or a cherry-pick of it"""
    for sha in bug_commits:
        result = git_in_repo(
            ["merge-base", "--is-ancestor", sha, ref], capture_output=True, text=True
        )
        if result.returncode == 0:
            return True
        if result.returncode != 1:
            raise BackportError(
                f"git merge-base failed checking {sha} against {ref}: {result.stderr}"
            )
    return False


def bug_commits_present(bug_commits: Iterable[str], branch: str) -> Set[str]:
    """
    Which of the bug commits are on the branch
    any_bug_commit_present stops at the first hit, this returns them all, so a
    caller can tell all of them are here from only the old ones are here
    """
    ref = f"origin/{branch}"
    return {
        sha
        for sha in bug_commits
        if git_in_repo(["merge-base", "--is-ancestor", sha, ref]).returncode == 0
    }
