# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""
Everything that talks to GitHub, through the gh CLI
Kept in one place so no command can grow a second, slightly different PR opener
"""

from util.config import BACKPORT_BRANCH_PREFIX, BackportError
from util.git import git, release_remote, run

import json
import re
import shutil
from functools import lru_cache
from typing import List, Optional, Tuple

# Where the pull requests are opened. Branches only go here when CI says so
AWS_LC_REPO = "aws/aws-lc"

_SLUG = re.compile(r"github\.com[:/]+([^/]+)/([^/]+?)(?:\.git)?/?$")


# --- The gh CLI ---


def gh(*args: str, check: bool = False):
    """
    Runs the GitHub CLI in this repo
    Returns the finished process. gh finds its own credentials: GH_TOKEN or
    GITHUB_TOKEN from the environment in CI, its stored login on a laptop, so
    nothing here has to know which one is in play
    """
    return run(["gh", *args], check=check)


def require_gh() -> None:
    """Raises unless the gh CLI is installed and logged in"""
    if shutil.which("gh") is None:
        raise BackportError(
            "the GitHub CLI (gh) is not installed, so no pull request can be opened.\n"
            "  Install it, or run without --open-pr and open them by hand."
        )
    if gh("auth", "status").returncode != 0:
        raise BackportError(
            "the GitHub CLI is not logged in.\n"
            "  Run 'gh auth login', or set GH_TOKEN."
        )


# --- Which Repo Is Which ---


def remote_slug(remote: str) -> Optional[str]:
    """
    The owner/repo a remote points at, or None when the URL cannot be read
    """
    url = git("remote", "get-url", remote, check=False)
    if url.returncode != 0:
        return None
    found = _SLUG.search(url.stdout.strip())
    return f"{found.group(1)}/{found.group(2)}" if found else None


def require_push_remote(remote: str, allow_aws_lc: bool = False) -> str:
    """
    Checks a remote is somewhere we are allowed to push branches
    Returns its owner/repo. aws/aws-lc is refused unless allow_aws_lc is set, which
    only CI does: running there, the checkout already is aws/aws-lc, so the branches
    have nowhere else to go. Locally the refusal stands, so a stray --remote cannot
    put half-reviewed work on the real repository
    """
    slug = remote_slug(remote)
    if slug is None:
        raise BackportError(f"no remote called '{remote}' in this checkout.")
    if slug.lower() == AWS_LC_REPO and not allow_aws_lc:
        raise BackportError(
            f"remote '{remote}' is {slug}, which is where the pull requests go, not\n"
            "  where the branches go. Push to your fork instead, with --remote."
        )
    return slug


@lru_cache(maxsize=1)
def fork_remote() -> str:
    """
    The remote backport branches are pushed to

    Returns the first remote that is not aws/aws-lc, preferring origin, else origin.
    A maintainer's origin is often aws/aws-lc itself, and that is never a push target
    """
    listed = git("remote", check=False)
    if listed.returncode != 0:
        return "origin"
    forks = [
        name
        for name in listed.stdout.split()
        if (remote_slug(name) or "").lower() != AWS_LC_REPO
    ]
    if "origin" in forks:
        return "origin"
    return forks[0] if forks else "origin"


def base_repo(override: Optional[str] = None) -> str:
    """
    Which repo the pull requests are opened against

    override: owner/repo from --base-repo, when given
    Returns the override, else the repo the release-branch remote points at, else
    aws/aws-lc. Read from the remote rather than a fixed name, so a staging repo and a
    checkout that calls it something other than upstream both work
    """
    return override or remote_slug(release_remote()) or AWS_LC_REPO


def head_spec(push_slug: str, base_slug: str, branch: str) -> str:
    """
    How to name the branch to GitHub, as owner:branch across repos or plain within one
    This is the only difference between a laptop pushing to a fork and CI pushing to
    the repo it is already running in
    """
    if push_slug.split("/")[0] == base_slug.split("/")[0]:
        return branch
    return f"{push_slug.split('/')[0]}:{branch}"


# --- Branches And Pull Requests ---


def push_branch(remote: str, branch: str) -> Optional[str]:
    """
    Pushes one local branch to the remote
    Returns None on success or the git error, so one bad branch cannot stop the rest
    Anything not named backport- is refused, so even the CI run that is allowed to
    push to aws/aws-lc can only push branches this tool built
    """
    if not branch.startswith(BACKPORT_BRANCH_PREFIX):
        raise BackportError(f"refusing to push '{branch}': not a backport branch.")
    pushed = git(
        "push", "--force-with-lease", remote, f"{branch}:{branch}", check=False
    )
    if pushed.returncode != 0:
        return (pushed.stderr or pushed.stdout).strip()
    return None


def existing_pr(repo: str, head: str) -> Optional[str]:
    """
    The URL of an open pull request already using this head branch, or None
    Checked before opening one so a second run does not file a duplicate
    """
    found = gh(
        "pr",
        "list",
        "--repo",
        repo,
        "--head",
        head,
        "--state",
        "open",
        "--json",
        "url",
        "--jq",
        ".[0].url // empty",
    )
    if found.returncode != 0:
        return None
    return found.stdout.strip() or None


def create_pr(repo: str, base: str, head: str, title: str, body: str) -> str:
    """
    Opens a pull request and returns its URL, or a string starting with 'error:'
    Never a draft: a backport nobody notices is the same as no backport
    """
    made = gh(
        "pr",
        "create",
        "--repo",
        repo,
        "--base",
        base,
        "--head",
        head,
        "--title",
        title,
        "--body",
        body,
    )
    if made.returncode != 0:
        return f"error: {(made.stderr or made.stdout).strip()}"
    return made.stdout.strip()


def comment_on_pr(repo: str, number: str, body: str) -> Optional[str]:
    """Leaves a comment on a pull request. Returns the error text, or None"""
    posted = gh("pr", "comment", str(number), "--repo", repo, "--body", body)
    if posted.returncode != 0:
        return (posted.stderr or posted.stdout).strip()
    return None


def pr_title_and_body(
    branch: str,
    fix: str,
    subject: str,
    basis: str,
    source_pr: Optional[str],
    fips_note: str = "",
) -> Tuple[str, str]:
    """
    The title and body for one backport pull request, as (title, body)
    fips_note, when the fix reaches inside the validated module, is put above everything
    else. A reviewer who reads one line of this has to read that one
    """
    title = f"[backport {branch}] {subject}"
    link = f" of #{source_pr}" if source_pr else ""
    warning = (
        f"> [!WARNING]\n> **FIPS boundary:** this fix {fips_note}.\n\n"
        if fips_note
        else ""
    )
    body = (
        f"{warning}"
        f"Backport{link} of `{fix[:12]}` onto `{branch}`.\n\n"
        f"- Verdict: **affected** ({basis or 'git history'}).\n"
        "- Cherry-picked as-is, with no changes beyond conflict resolution.\n"
        "- **Not** auto-merged. Please review before merging.\n"
        + ("- Needs FIPS review before merging.\n" if fips_note else "")
        + "\n_Opened by the AWS-LC backport tool._"
    )
    return title, body


def summary_lines(
    fix: str,
    subject: str,
    results: List[Tuple[str, str, str]],
    fips_note: str = "",
) -> str:
    """
    A markdown table of what happened to each branch, for a comment on the source PR
    results is (branch, outcome, detail)
    Carries the same FIPS boundary warning as the pull request bodies, since this comment
    is what the author of the fix actually reads
    """
    lines = [
        f"### Backport report for `{fix[:12]}`",
        "",
        f"{subject}",
        "",
    ]
    if fips_note:
        lines += [f"> [!WARNING]\n> **FIPS boundary:** this fix {fips_note}.", ""]
    lines += [
        "| Branch | Result |",
        "| --- | --- |",
    ]
    for branch, outcome, detail in results:
        lines.append(f"| `{branch}` | {outcome}: {detail} |")
    lines += ["", "Nothing is auto-merged. Every pull request above needs review."]
    if fips_note:
        lines.append("Every branch above also needs FIPS review before it merges.")
    return "\n".join(lines)


# Marks our JSON so resolve can tell it from any other fenced block in the comment.
# Bump the version if the shape changes
PLAN_KEY = "backport_plan"
PLAN_VERSION = 1


def plan_block(fix: str, results: List[Tuple[str, str, str]]) -> str:
    """
    The run as JSON, folded into the comment so resolve can read it back
    When CI did the analysis there is no saved run on the reviewer's machine, so this
    is the only way 'backport resolve --pr N' can know which branches were flagged
    """
    payload = {
        PLAN_KEY: PLAN_VERSION,
        "fix": fix,
        "branches": {b: o for b, o, _ in results},
    }
    blob = json.dumps(payload, indent=2)
    return (
        "<details>\n<summary>backport plan (read by <code>backport resolve</code>)"
        f"</summary>\n\n```json\n{blob}\n```\n\n</details>"
    )


def read_plan(repo: str, number: str) -> Optional[dict]:
    """
    The most recent backport plan on a pull request, or None when there is none
    Returns the parsed payload. A comment that is not ours, or not valid JSON, is
    skipped rather than raising, since anyone may comment anything on a pull request
    """
    got = gh(
        "pr",
        "view",
        str(number),
        "--repo",
        repo,
        "--json",
        "comments",
        "--jq",
        ".comments[].body",
    )
    if got.returncode != 0:
        return None
    found = None
    for blob in re.findall(r"```json\s*(\{.*?\})\s*```", got.stdout, re.DOTALL):
        try:
            payload = json.loads(blob)
        except json.JSONDecodeError:
            continue
        if payload.get(PLAN_KEY) == PLAN_VERSION:
            found = payload  # keep going, the last one is the newest
    return found
