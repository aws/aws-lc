#!/usr/bin/env python3
"""
backport - local, patch-driven CLI for the AWS-LC backport bot.

Layer: entrypoint. Wires the command modules (analyze / apply / ci / resolve /
clear) into one argument parser and dispatches to them.

Works from a PATCH rather than a merged commit, so an embargoed fix can be
assessed -- and backported to local branches -- before any public code change.
See README.md for what each subcommand does; every flag is documented in its
``--help``.

Module map: gitutil = git plumbing + repo targeting; patches = patch->commit +
source resolution; runstate = analyze->apply cache; verdicts = deterministic
bucketing + AI passes; render = output; engine + ai = the impact core.
"""

import argparse
import sys
from typing import Optional, Sequence

from analyze import cmd_analyze
from apply import cmd_apply, cmd_clear
from ci import cmd_ci
from common import BackportError
from gitutil import resolve_patch_path, target_repo
from resolve import cmd_resolve


# --------------------------------------------------------------------------
# Argument parser
# --------------------------------------------------------------------------


def add_common(p: argparse.ArgumentParser) -> None:
    """Flags shared by every subcommand."""
    p.add_argument(
        "--repo",
        help="path to the AWS-LC checkout to operate on (default: "
        "$BACKPORT_REPO_PATH, else the current directory)",
    )
    p.add_argument(
        "--base", help="base ref to apply the patch on (default origin/main)"
    )
    p.add_argument(
        "--3way",
        dest="three_way",
        action="store_true",
        help="use 3-way apply/am when the base has drifted",
    )


def add_analyze(sub) -> None:
    p = sub.add_parser(
        "analyze", help="give an affected / not affected verdict for every branch"
    )
    p.add_argument(
        "--commit",
        help="analyze an existing commit instead of a patch/working tree; the fix "
        "is reconstructed internally (base defaults to <commit>^). Accepts a "
        "range for fixes split across commits: A..B, or A...B (e.g. "
        "origin/main...HEAD) analyzes the net change of the whole span",
    )
    p.add_argument(
        "--yes",
        action="store_true",
        help="skip the interactive test-file confirmation (for scripted/CI runs)",
    )
    p.add_argument("--branches", nargs="+", help="limit to these branches")
    p.add_argument(
        "--no-ai",
        action="store_true",
        help="deterministic only; do not consult the AI on inconclusive branches "
        "(they are flagged AFFECTED for review instead)",
    )
    p.add_argument("--json", action="store_true", help="emit JSON")
    add_common(p)
    p.set_defaults(func=cmd_analyze)


def add_apply(sub) -> None:
    p = sub.add_parser("apply", help="cherry-pick the patch onto local branches")
    p.add_argument("--branches", nargs="+", help="branches to apply to")
    p.add_argument(
        "--all-affected", action="store_true", help="apply to every AFFECTED branch"
    )
    p.add_argument(
        "--commit",
        help="apply an existing commit instead of the last analyzed run "
        "(base defaults to <commit>^); also accepts a range A..B / A...B for a "
        "multi-commit fix (applied as its net change)",
    )
    p.add_argument("--yes", action="store_true", help="skip the confirmation prompt")
    p.add_argument(
        "--in-place",
        dest="in_place",
        action="store_true",
        help="(default) when conflicts are resolved, check each branch out in your "
        "current repo so your IDE shows it; --worktree uses an isolated worktree",
    )
    p.add_argument(
        "--worktree",
        dest="in_place",
        action="store_false",
        help="resolve conflicts in an isolated throwaway worktree, not your checkout",
    )
    p.add_argument(
        "--keep-patch",
        action="store_true",
        help="do not delete the patch file / cached run after a clean apply",
    )
    add_common(p)
    p.set_defaults(func=cmd_apply, in_place=True)


def add_ci(sub) -> None:
    p = sub.add_parser(
        "ci",
        help="post-merge: open backport PRs on the fork for a merged commit",
    )
    p.add_argument("--commit", required=True, help="merged commit SHA to back-port")
    p.add_argument("--pr", help="source PR number (for cross-linking / comments)")
    p.add_argument(
        "--remote",
        default="origin",
        help="fork remote to push branches / open PRs on (default origin)",
    )
    p.add_argument(
        "--no-ai",
        action="store_true",
        help="deterministic only; do not consult the AI (default: AI on)",
    )
    p.add_argument(
        "--dry-run",
        action="store_true",
        help="analyze and cherry-pick locally but do not push or open PRs",
    )
    add_common(p)
    p.set_defaults(func=cmd_ci, json=False)


def add_resolve(sub) -> None:
    p = sub.add_parser(
        "resolve",
        help="interactively resolve backport conflicts locally, one PR per branch",
    )
    p.add_argument("--commit", help="fix commit SHA to backport")
    p.add_argument("--pr", help="source PR number to backport (resolved via gh)")
    p.add_argument(
        "--remote",
        default="upstream",
        help="fork remote to push branches / open PRs on (default origin)",
    )
    add_common(p)
    p.set_defaults(func=cmd_resolve, json=False, in_place=True, no_ai=True)


def add_clear(sub) -> None:
    p = sub.add_parser(
        "clear",
        help="remove the saved run state (.backport-runs/) from the tool folder",
    )
    add_common(p)
    p.set_defaults(func=cmd_clear)


def build_parser() -> argparse.ArgumentParser:
    """Build the ``backport`` argument parser (analyze / apply / ci / clear)."""
    ap = argparse.ArgumentParser(
        prog="backport",
        description="Local, patch-driven AWS-LC backport impact analysis + apply.",
    )
    sub = ap.add_subparsers(dest="cmd", required=True)
    add_analyze(sub)
    add_apply(sub)
    add_ci(sub)
    add_resolve(sub)
    add_clear(sub)
    return ap


# --------------------------------------------------------------------------
# Entrypoint
# --------------------------------------------------------------------------


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        repo_top = target_repo(args)
        resolve_patch_path(args, repo_top)
        return args.func(args)
    except BackportError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
