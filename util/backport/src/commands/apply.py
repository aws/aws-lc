"""
The `apply` and `clear` commands.

`apply` cherry-picks the fix onto local `backport/<branch>/<id>` branches so you can
review them. It never pushes, opens a PR, or merges anything. If a cherry-pick
conflicts it hands off to `resolve`.

`clear` deletes the saved run.
"""

import shutil
import sys
from typing import List, Sequence, Tuple

from engine.analysis import get_supported_branches, sort_branches
from util.config import AFFECTED, BackportError
from util.git import cherry_pick_local, git, ref_exists, resolve_fix_commit
from util.render import print_section
from commands.resolve import conflict_lines, run_resolution
from util.config import load_run, run_dir
from engine.analysis import analyze_branches


def resolve_apply_target(args) -> "Tuple[str, dict]":
    """Which fix to apply, as ``(sha, saved_run)``.

    `--commit` wins and ignores the cache. Otherwise reuse the last `analyze`, so
    the normal flow is `analyze` then a bare `apply --all-affected`.
    """
    if getattr(args, "commit", None):
        return resolve_fix_commit(args)[0], {}
    run = load_run()
    fix_sha = run.get("fix", "")
    if not fix_sha or not ref_exists(fix_sha):
        raise BackportError(
            f"the analyzed commit ({fix_sha[:10] or 'unknown'}) is no longer in "
            "this checkout. Re-run `backport analyze`, or pass --commit <ref>."
        )
    return fix_sha, run


def run_cherry_picks(
    fix_sha: str, targets: Sequence[str]
) -> "Tuple[List[str], List[str], List[str]]":
    """Cherry-pick the fix onto each target branch, printing per-branch status.

    Returns ``(clean, conflict, errors)`` as lists of branch names.
    """
    run_id = fix_sha[:8]
    clean: List[str] = []
    conflict: List[str] = []
    errors: List[str] = []
    for branch in targets:
        status, detail, extra = cherry_pick_local(fix_sha, branch, run_id)
        print(f"\n── {branch} " + "─" * max(0, 50 - len(branch)))
        if status == "clean":
            if extra:
                print("  Clean — test-only conflict auto-resolved (test hunk dropped):")
                for line in conflict_lines(extra):
                    print(line)
            else:
                print("  Clean cherry-pick.")
            print(f"  branch: {detail}")
            clean.append(branch)
        elif status == "conflict":
            print("  CONFLICT — this backport must be resolved:")
            for line in conflict_lines(extra):
                print(line)
            conflict.append(branch)
        else:
            print(f"  error: {detail}")
            errors.append(branch)
    return clean, conflict, errors


def select_targets(args, buckets):
    """Which branches to cherry-pick onto: --branches, or --all-affected.

    Returns a chronologically sorted list, or None if neither flag was given
    (the caller turns that into a usage error).
    """
    if args.branches:
        return sort_branches(args.branches)
    if args.all_affected:
        return sort_branches(b for b, s in buckets.items() if s == AFFECTED)
    return None


def cmd_apply(args) -> int:
    """Cherry-pick the fix onto local branches, then (interactively) open a PR
    per branch -- resolving any conflicts along the way.

    Targets come from --branches, or --all-affected (the AFFECTED branches from
    the last analyze). Clean picks land as local ``backport/<branch>/<id>``
    branches; conflicts are resolved via the interactive hand-off. In an
    interactive terminal it finishes by offering to open one PR per prepared
    branch (clean + resolved); non-interactively it just reports and leaves the
    local branches for review.
    """
    fix_sha, run = resolve_apply_target(args)
    branches = run.get("branches") or get_supported_branches()
    buckets = run.get("buckets") or analyze_branches(fix_sha, branches)[2]

    targets = select_targets(args, buckets)
    if targets is None:
        print(
            "Specify what to apply: --all-affected, or --branches <name..>.",
            file=sys.stderr,
        )
        return 2
    if not targets:
        print("Nothing to apply (no matching branches).")
        return 0

    # Show the plan and confirm before touching anything.
    print("Will cherry-pick the fix onto local branches:")
    for b in targets:
        print(f"  - {b}  ->  backport/{b}/{fix_sha[:8]}")
    if not args.yes:
        if not sys.stdin.isatty():
            print("\nRefusing to proceed without --yes in a non-interactive shell.")
            return 3
        if input("\nProceed? [y/N] ").strip().lower() not in ("y", "yes"):
            print("Aborted.")
            return 0

    print()
    clean, conflict, errors = run_cherry_picks(fix_sha, targets)
    subject = git("log", "-1", "--format=%s", fix_sha).stdout.strip()

    # Interactive: resolve any conflicts, then open one PR per prepared branch
    # (clean cherry-picks + resolved conflicts) -- the full local pipeline.
    if sys.stdin.isatty() and (clean or conflict):
        return run_resolution(
            args,
            fix_sha,
            subject,
            buckets,
            sort_branches(conflict),
            source_pr=None,
            clean_local=clean,
        )

    # Non-interactive: report and leave the local branches for review.
    print("\n" + "─" * 52)
    print("Summary\n")
    print_section("Clean (local backport branches)", clean or ["(none)"])
    print_section("Conflicts (need resolution)", conflict or ["(none)"])
    if errors:
        print_section("Errors", errors)
    if conflict:
        print(f"Resolve them with:  backport resolve --commit {fix_sha[:12]}")
    print(
        "\nNothing was pushed (non-interactive). Inspect `git branch --list "
        "'backport/*'`."
    )
    return 0


def cmd_clear(args) -> int:
    """Remove the saved run state (.backport-runs/) from the tool folder."""
    directory = run_dir()
    if directory.exists():
        shutil.rmtree(directory, ignore_errors=True)
        print(f"Removed {directory}")
    else:
        print(f"Nothing to clear ({directory} does not exist).")
    return 0
