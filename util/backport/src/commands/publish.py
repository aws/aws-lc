# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""
The publish command: pushes the branches apply built and opens one pull request each
Run by apply after a local cherry-pick, or on its own in CI
"""

from commands.apply import backport_branch_name, branches_to_backport, load_run
from util.config import BackportError, fips_boundary_note
from util.git import (
    WORKTREE_ROOT,
    branch_exists,
    branch_ref,
    cherry_pick_in_progress,
    commit_subject,
    commits_ahead,
    remove_worktree,
)
from util.github import (
    base_repo,
    comment_on_pr,
    create_pr,
    existing_pr,
    head_spec,
    pr_title_and_body,
    push_branch,
    require_gh,
    require_push_remote,
    summary_lines,
)
from util.render import ask_yn

from typing import Dict, List, Optional, Tuple

# What happened to one branch
OPENED = "opened"
ALREADY_OPEN = "already open"
UNFINISHED = "unfinished"
MISSING = "missing"
FAILED = "failed"
DRY_RUN = "dry run"


def fips_note_for(run: Dict) -> str:
    """
    The FIPS boundary line for this run, or empty when the fix stayed outside the module

    run: the saved analyze run
    Returns the same sentence analyze printed, since publish never reads the diff itself
    and the file list it needs was recorded for it
    """
    return fips_boundary_note(run.get("fips_files", []))


def branch_state(release: str, local_branch: str) -> str:
    """
    Whether one backport branch is ready to become a pull request
    Returns MISSING when apply never made it, UNFINISHED while a cherry-pick is still
    stopped in its worktree, and OPENED when it holds at least one commit. Resolving a
    conflict by hand is enough to turn UNFINISHED into ready, with no need to re-run
    apply

    The commit count is measured against the same ref apply cut the branch from, so a
    branch carrying no pick of its own cannot look ready just because the fork it was
    compared against is behind
    """
    if not branch_exists(local_branch):
        return MISSING
    worktree = WORKTREE_ROOT / local_branch
    if worktree.exists() and cherry_pick_in_progress(worktree):
        return UNFINISHED
    if commits_ahead(branch_ref(release), local_branch) < 1:
        return MISSING
    return OPENED


def publish_branch(
    release: str,
    fix: str,
    subject: str,
    basis: str,
    source_pr: Optional[str],
    remote: str,
    push_slug: str,
    repo: str,
    dry_run: bool,
    fips_note: str = "",
) -> Tuple[str, str]:
    """
    Pushes one finished backport branch and opens its pull request
    Returns (outcome, detail) where detail is a URL, a reason, or an error
    """
    local_branch = backport_branch_name(fix, release)
    state = branch_state(release, local_branch)
    if state == MISSING:
        return MISSING, f"no branch {local_branch}, run apply first"
    if state == UNFINISHED:
        return UNFINISHED, f"cherry-pick still open in {WORKTREE_ROOT / local_branch}"

    head = head_spec(push_slug, repo, local_branch)
    open_already = existing_pr(repo, head)
    if open_already:
        return ALREADY_OPEN, open_already
    if dry_run:
        return DRY_RUN, f"would push {local_branch} and open a PR into {release}"

    failure = push_branch(remote, local_branch)
    if failure:
        return FAILED, f"push failed: {failure}"

    title, body = pr_title_and_body(release, fix, subject, basis, source_pr, fips_note)
    url = create_pr(repo, release, head, title, body)
    if url.startswith("error:"):
        return FAILED, url
    # The worktree only survives a resolved conflict, and it is finished with now
    remove_worktree(WORKTREE_ROOT / local_branch)
    return OPENED, url


def run_publish(
    run: Dict,
    branches: List[str],
    remote: str,
    push_slug: str,
    source_pr: Optional[str],
    dry_run: bool,
) -> List[Tuple[str, str, str]]:
    """
    Publishes every named branch
    Returns (branch, outcome, detail) per branch, in the order given. The caller has
    already checked gh and the remote, so nothing here can fail on setup
    """
    repo = base_repo("upstream")
    fix = run["fix"]
    subject = commit_subject(fix)
    decided = run.get("decided_by", {})
    # Recorded by analyze, so a fix that reaches into the validated module is still
    # called out here even though publish never looks at the diff itself
    fips_note = fips_note_for(run)

    outcomes = []
    for release in branches:
        outcome, detail = publish_branch(
            release=release,
            fix=fix,
            subject=subject,
            basis=decided.get(release, ""),
            source_pr=source_pr,
            remote=remote,
            push_slug=push_slug,
            repo=repo,
            dry_run=dry_run,
            fips_note=fips_note,
        )
        outcomes.append((release, outcome, detail))
        print(f"  {release}: {outcome}: {detail}")
    return outcomes


def report(
    run: Dict,
    outcomes: List[Tuple[str, str, str]],
    source_pr: Optional[str],
    repo: str,
    dry_run: bool = False,
) -> None:
    """
    Prints the tally and, when a source PR was named, comments the table on it
    A dry run prints the comment instead of posting it. Writing to a real pull request
    is the one thing a dry run must not do, and the source PR is somebody else's
    """
    opened = sum(1 for _, o, _ in outcomes if o == OPENED)
    would_open = sum(1 for _, o, _ in outcomes if o == DRY_RUN)
    stuck = [b for b, o, _ in outcomes if o in (UNFINISHED, MISSING, FAILED)]
    print()
    if would_open:
        # Without this a dry run reports "0 pull request(s) opened", which reads as
        # nothing to do rather than nothing done yet
        print(
            f"dry run: {would_open} pull request(s) would be opened, "
            f"{len(stuck)} still need attention"
        )
    else:
        print(f"{opened} pull request(s) opened, {len(stuck)} still need attention")
    if stuck:
        print(f"  {', '.join(stuck)}")
        # The advice has to match the cause, or it sends people to the wrong place
        kinds = {o for _, o, _ in outcomes}
        if MISSING in kinds:
            print("  Missing branches: run 'backport apply' first.")
        if UNFINISHED in kinds:
            print(
                "  Unfinished branches: resolve the conflict in the worktree, then\n"
                "  'git cherry-pick --continue' there and run publish again."
            )
        if FAILED in kinds:
            print("  Failed branches: see the reason above.")
    if source_pr:
        table = summary_lines(
            run["fix"],
            commit_subject(run["fix"]),
            outcomes,
            fips_note_for(run),
        )
        if dry_run:
            print()
            print(f"dry run: would comment this on #{source_pr}")
            print(table)
            return
        failure = comment_on_pr(repo, source_pr, table)
        if failure:
            print(f"could not comment on #{source_pr}: {failure}")


def cmd_publish(args) -> int:
    """
    Opens a backport pull request for every affected branch
    Returns 0 when every branch was published or already had a pull request, 1 when
    any branch still needs attention
    """
    run = load_run()
    branches = branches_to_backport(run["verdicts"], args.branch)
    if not branches:
        print("No affected branches in the last analyze run, nothing to publish.")
        return 0

    # Checked before anything is printed, so nobody confirms a run that cannot work
    require_gh()
    push_slug = require_push_remote(args.remote, args.push_to_aws_lc)

    repo = base_repo("upstream")
    print(f"Fix {run['fix'][:10]}")
    print(f"Opening pull requests into {repo} for: {', '.join(branches)}")
    print(f"Branches are pushed to '{args.remote}'")
    if not args.yes and not args.dry_run and not ask_yn("Go ahead?"):
        print("Aborted. Nothing was pushed.")
        return 0

    outcomes = run_publish(run, branches, args.remote, push_slug, args.pr, args.dry_run)
    report(run, outcomes, args.pr, repo, args.dry_run)
    return 1 if any(o in (UNFINISHED, MISSING, FAILED) for _, o, _ in outcomes) else 0


def offer_publish(run: Dict, branches: List[str], remote: str) -> None:
    """
    Asks whether to open the pull requests, straight after apply cherry-picked
    Only the branches that applied cleanly are offered, so a conflict is never
    published half-done
    """
    if not branches:
        return
    print()
    # Checked before the question, so a missing gh is not discovered after a yes
    try:
        require_gh()
        push_slug = require_push_remote(remote)
    except BackportError as exc:
        print(f"Cannot open pull requests: {exc}")
        print("The branches are here. Fix that and run 'backport publish'.")
        return
    if not ask_yn(f"Open pull requests for {len(branches)} branch(es)?"):
        print("Left as local branches. Run 'backport publish' when you are ready.")
        return
    outcomes = run_publish(
        run, branches, remote, push_slug, source_pr=None, dry_run=False
    )
    report(run, outcomes, None, base_repo("upstream"))
