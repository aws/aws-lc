# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""
The apply command: cherry-picks the fix onto one local branch per affected branch
Nothing is pushed and no pull request is opened, the branches are yours to review
"""

from util.config import (
    AFFECTED,
    BACKPORT_BRANCH_PREFIX,
    RUN_FILE,
    UNSURE,
    BackportError,
)
from util.git import (
    WORKTREE_ROOT,
    abort_cherry_pick,
    add_worktree,
    branch_exists,
    branch_ref,
    cherry_pick,
    cherry_pick_was_empty,
    commit_exists,
    remove_worktree,
)
from util.render import ask_yn

import json
from typing import Dict, List, Optional, Tuple

# How one branch turned out
APPLIED = "applied"
CONFLICT = "conflict"
ALREADY_THERE = "already there"
BRANCH_EXISTS = "branch exists"


def load_run() -> dict:
    """
    The run analyze saved, as {generated_at, fix, base, branches, verdicts}
    Written by save_run in util/config.py, where the fields are spelled out

    Raises rather than returning a partial answer, in all three cases where acting on
    the run would mean guessing: there is no run, the file cannot be read, or the fix
    it names is no longer in this checkout
    """
    try:
        run = json.loads(RUN_FILE.read_text(encoding="utf-8"))
    except FileNotFoundError:
        raise BackportError(
            "no saved analyze run to apply.\n  Run 'backport analyze' first."
        )
    except json.JSONDecodeError as exc:
        raise BackportError(f"{RUN_FILE} is not valid JSON: {exc}")

    # These two are the whole input: which commit to pick, and onto which branches
    for key in ("fix", "verdicts"):
        if key not in run:
            raise BackportError(f"{RUN_FILE} has no '{key}'. Re-run analyze.")

    # Analyzing a range squashes it into a commit nothing points at, so git can collect
    # it between analyze and apply
    if not commit_exists(run["fix"]):
        raise BackportError(
            f"the analyzed fix {run['fix'][:10]} is not in this checkout any more.\n"
            "  Re-run analyze."
        )
    return run


def backport_branch_name(fix: str, release: str) -> str:
    """What the local branch holding a backport is called"""
    return f"{BACKPORT_BRANCH_PREFIX}{release}-{fix[:10]}"


def branches_to_backport(verdicts: Dict[str, str], only: Optional[str]) -> List[str]:
    """
    Which release branches to cherry-pick onto
    Returns the affected ones, or just the named branch. Unsure branches are left
    out: analyze could not settle them, so a cherry-pick would be a guess
    """
    if only:
        if only not in verdicts:
            known = ", ".join(sorted(verdicts))
            raise BackportError(f"'{only}' was not in the analyze run.\n  Had: {known}")
        return [only]
    return [b for b, state in verdicts.items() if state == AFFECTED]


def cherry_pick_onto(fix: str, release: str) -> Tuple[str, List[str]]:
    """
    Cherry-picks the fix onto one release branch, in a worktree of its own
    Returns (outcome, conflicting files) where outcome is one of the four above

    The worktree is what makes this safe to run while you are working: your own
    checkout never moves. It is removed once the pick is settled either way, and kept
    only when there is a conflict, because that is where you resolve it

    The pick starts from the same remote-tracking ref analyze judged, not from origin.
    A fork is often behind on the release branches, and starting from a stale one would
    build the backport on the wrong base
    """
    local_branch = backport_branch_name(fix, release)
    if branch_exists(local_branch):
        return BRANCH_EXISTS, []

    worktree = WORKTREE_ROOT / local_branch
    add_worktree(worktree, local_branch, branch_ref(release))
    picked, conflicts = cherry_pick(worktree, fix)

    if picked:
        remove_worktree(worktree)
        return APPLIED, []
    if not conflicts and cherry_pick_was_empty(worktree):
        # The pick came out empty, so this branch already has the change
        abort_cherry_pick(worktree)
        remove_worktree(worktree)
        return ALREADY_THERE, []
    return CONFLICT, conflicts


def cmd_apply(args) -> int:
    """
    Cherry-picks the analyzed fix onto every affected branch
    Returns 0 when every branch applied cleanly or was skipped, 1 when any conflicted
    """
    run = load_run()
    fix, verdicts = run["fix"], run["verdicts"]
    releases = branches_to_backport(verdicts, args.branch)

    if not releases:
        print("No affected branches in the last analyze run, nothing to apply.")
        return 0

    unsure = [b for b, state in verdicts.items() if state == UNSURE]
    print(f"Fix {fix[:10]}, analyzed {run.get('generated_at', 'at an unknown time')}")
    print(f"Backporting onto {len(releases)} branch(es): {', '.join(releases)}")
    if unsure:
        print(
            f"Leaving out {len(unsure)} branch(es) analyze could not settle: "
            f"{', '.join(unsure)}"
        )
    if not args.yes and not ask_yn("Create these local branches?"):
        print("Aborted. Nothing was created.")
        return 0

    outcomes = {}
    for release in releases:
        outcome, conflicts = cherry_pick_onto(fix, release)
        outcomes[release] = (outcome, conflicts)
        local_branch = backport_branch_name(fix, release)
        if outcome == APPLIED:
            print(f"  {release}: applied, on {local_branch}")
        elif outcome == BRANCH_EXISTS:
            print(f"  {release}: skipped, {local_branch} already exists")
        elif outcome == ALREADY_THERE:
            print(f"  {release}: nothing to do, the change is already there")
        else:
            print(f"  {release}: CONFLICT in {len(conflicts)} file(s)")
            for name in conflicts:
                print(f"      {name}")
            print(f"      resolve in {WORKTREE_ROOT / local_branch}")

    conflicted = [b for b, (o, _) in outcomes.items() if o == CONFLICT]
    print()
    print(f"{len(outcomes) - len(conflicted)} of {len(outcomes)} applied cleanly")
    if conflicted:
        print(
            "Resolve each conflict in the worktree named above, then "
            "'git cherry-pick --continue' there."
        )
    print("Nothing was pushed. Review each branch before you open a pull request.")
    return 1 if conflicted else 0
