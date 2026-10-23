# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""
The resolve command: walks the conflicts apply left behind, one branch at a time
Takes its list of branches from the last local run, or from the report the bot left
on a pull request, which is the only thing a reviewer has when CI did the analysis
"""

from commands.apply import backport_branch_name, branches_to_backport, load_run
from commands.publish import branch_state, offer_publish, UNFINISHED
from util.config import BackportError
from util.git import (
    WORKTREE_ROOT,
    continue_cherry_pick,
    files_with_conflict_markers,
    staged_files,
    unmerged_files,
)
from util.github import base_repo, read_plan
from util.render import ask_yn

from typing import Dict, Tuple

# What happened to one branch
FINISHED = "finished"
LEFT = "left alone"
STILL_STUCK = "still stuck"
NOTHING_TO_DO = "nothing to do"


def run_from_pr(number: str) -> Dict:
    """
    The run the bot recorded on a pull request, as a run-shaped dict
    Returns {"fix": sha, "verdicts": {...}}. Raises when the pull request carries no
    plan, since guessing which branches were flagged would be worse than stopping
    """
    plan = read_plan(base_repo("upstream"), number)
    if plan is None:
        raise BackportError(
            f"no backport plan found on #{number}.\n"
            "  Only a pull request the bot has reported on carries one."
        )
    return {
        "fix": plan["fix"],
        # Every branch the bot touched is offered, and branch_state decides which of
        # them still need work
        "verdicts": {b: "affected" for b in plan.get("branches", {})},
    }


def resolve_branch(release: str, local_branch: str) -> Tuple[str, str]:
    """
    Walks one conflicted branch: shows the files, waits, then finishes the pick
    Returns (outcome, detail)
    """
    worktree = WORKTREE_ROOT / local_branch
    stuck = unmerged_files(worktree)
    print()
    print(f"{release}")
    print(f"  worktree: {worktree}")
    if stuck:
        print(f"  {len(stuck)} file(s) still conflicting:")
        for name in stuck:
            print(f"    {name}")
    print("  Fix them there and 'git add' each one. Nothing is committed until you")
    print("  say so, and the pick is only finished once git sees nothing unmerged.")

    while True:
        if not ask_yn("  Resolved?"):
            return LEFT, "come back to it with 'backport resolve'"
        # git's own view first. A delete or rename conflict carries no markers, so a
        # marker check alone would pass it and keep one side silently
        still = unmerged_files(worktree)
        if still:
            print(f"  git still calls {len(still)} file(s) unmerged:")
            for name in still:
                print(f"    {name}")
            print("  Choose a side, then 'git add' each of them.")
            continue
        markers = files_with_conflict_markers(
            worktree, sorted(set(stuck) | set(staged_files(worktree)))
        )
        if markers:
            # git will commit a file with the markers still in it
            print(f"  These still have conflict markers: {', '.join(markers)}")
            continue
        failure = continue_cherry_pick(worktree)
        if failure:
            print(f"  git could not finish it: {failure}")
            continue
        return FINISHED, f"{local_branch} is ready"


def cmd_resolve(args) -> int:
    """
    Finishes the conflicted backports, then offers to open their pull requests
    Returns 0 when nothing is left conflicting, 1 when a branch was left alone
    """
    run = run_from_pr(args.pr) if args.pr else load_run()
    branches = branches_to_backport(run["verdicts"], args.branch)
    fix = run["fix"]

    stuck = [
        b
        for b in branches
        if branch_state(b, backport_branch_name(fix, b)) == UNFINISHED
    ]
    if not stuck:
        print("Nothing is waiting on a conflict.")
        if args.pr:
            print("Run 'backport apply' first if the branches are not here yet.")
        return 0

    print(f"Fix {fix[:10]}, {len(stuck)} branch(es) to resolve: {', '.join(stuck)}")
    outcomes = {}
    for release in stuck:
        outcomes[release] = resolve_branch(release, backport_branch_name(fix, release))

    finished = [b for b, (o, _) in outcomes.items() if o == FINISHED]
    left = [b for b, (o, _) in outcomes.items() if o != FINISHED]
    print()
    print(f"{len(finished)} of {len(stuck)} resolved")
    if left:
        print(f"Still conflicting: {', '.join(left)}")

    if finished:
        offer_publish(run, finished, args.remote)
    return 1 if left else 0
