# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""
Finds the release branches to check and puts them in order
Independent of the rest of the engine, only the analyze command calls it
"""

from util.config import SUPPORTED_BRANCH_PREFIXES, BackportError, out_of_support
from util.git import git_in_repo, release_remote

import re
from typing import Iterable, List, Tuple


def remote_branch_names() -> List[str]:
    """Release-remote branch names from `git branch -r`, without the remote prefix"""
    remote = release_remote()
    result = git_in_repo(["branch", "-r"], capture_output=True, text=True)
    if result.returncode != 0:
        raise BackportError(f"git branch -r failed: {result.stderr}")
    names = []
    for line in result.stdout.splitlines():
        line = line.strip()
        if " -> " in line or not line.startswith(f"{remote}/"):
            continue
        names.append(line[len(remote) + 1 :])
    return names


def branch_date_key(name: str) -> str:
    """The YYYY-MM-DD in the branch name, or empty when it has none"""
    match = re.search(r"\d{4}-\d{2}-\d{2}", name)
    return match.group(0) if match else ""


def sort_branches(names: Iterable[str]) -> List[str]:
    """
    Newest to oldest by the date in the name, undated last
    Returns a new sorted list
    """
    return sorted(
        names, key=lambda n: (branch_date_key(n) or "0000-00-00", n), reverse=True
    )


def get_supported_branches(
    apply_support_window: bool = True,
) -> Tuple[List[str], List[Tuple[str, str]]]:
    """
    Release branches to check, newest first, matched on name prefix
    Returns (branches, dropped) where dropped is (branch, why) for each one past its
    end of support. Dropped branches are reported rather than just left out: a branch
    quietly missing from the table looks the same as a branch nobody needed to fix

    apply_support_window is off for the replay bench, which grades fixes from years
    ago against branches that were in support then, not now
    """
    found = sort_branches(
        name
        for name in remote_branch_names()
        if name.startswith(SUPPORTED_BRANCH_PREFIXES)
    )
    if not apply_support_window:
        return found, []
    branches, dropped = [], []
    for name in found:
        why = out_of_support(name)
        if why:
            dropped.append((name, why))
        else:
            branches.append(name)
    return branches, dropped
