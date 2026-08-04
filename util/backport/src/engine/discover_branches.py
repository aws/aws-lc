"""
Finds the release branches to check and puts them in order
Independent of the rest of the engine, only the analyze command calls it
"""

from util.config import SUPPORTED_BRANCH_PREFIXES, BackportError
from util.git import git_in_repo

import re
from typing import Iterable, List


def remote_branch_names() -> List[str]:
    """Branch names from `git branch -r`, without the origin/ prefix"""
    result = git_in_repo(["branch", "-r"], capture_output=True, text=True)
    if result.returncode != 0:
        raise BackportError(f"git branch -r failed: {result.stderr}")
    names = []
    for line in result.stdout.splitlines():
        line = line.strip()
        if " -> " in line or not line.startswith("origin/"):
            continue
        names.append(line[len("origin/") :])
    return names


def branch_date_key(name: str) -> str:
    """The YYYY-MM-DD in the branch name, or empty when it has none"""
    match = re.search(r"\d{4}-\d{2}-\d{2}", name)
    return match.group(0) if match else ""


def sort_branches(names: Iterable[str]) -> List[str]:
    """Newest to oldest by the date in the name, undated last"""
    return sorted(
        names, key=lambda n: (branch_date_key(n) or "0000-00-00", n), reverse=True
    )


def get_supported_branches() -> List[str]:
    """Release branches to check, newest first, matched on name prefix"""
    return sort_branches(
        name
        for name in remote_branch_names()
        if f"origin/{name}".startswith(SUPPORTED_BRANCH_PREFIXES)
    )
