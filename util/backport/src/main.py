#!/usr/bin/env python3
"""
backport - decide which AWS-LC release branches a fix belongs on, then back-port it.

Builds the argument parser and hands off to the command modules.

Works on real commits: name a fix with `--commit <ref>` (or a range, for a fix split
across several commits), or say nothing and it uses your branch's commits since it
left the mainline -- so you can check a fix before it merges. See README.md for what
each subcommand does, and `--help` for the flags.

Where things live: util/ = constants, git, output. engine/analysis = the verdict.
engine/ai = the advisory layer. commands/ = one file per subcommand.
"""

import argparse
import sys
from typing import Optional, Sequence

from commands.analyze import cmd_analyze
from commands.apply import cmd_apply, cmd_clear
from commands.publish import cmd_publish
from commands.resolve import cmd_resolve
from util.config import BackportError
from util.git import target_repo


# --- Argument parser ------------------------------------------------------

# --commit accepts a single ref or a range; documented once and shared, since
# analyze / apply / resolve all take the same thing.
_COMMIT_HELP = (
    "the fix to back-port: a commit ref, or a range A..B / A...B (e.g. "
    "origin/main...HEAD) for a fix split across several commits, analyzed as its "
    "net change"
)


def add_common(p: argparse.ArgumentParser) -> None:
    """Flags shared by every subcommand."""
    p.add_argument(
        "--repo",
        help="path to the AWS-LC checkout to operate on (default: "
        "$BACKPORT_REPO_PATH, else the current directory)",
    )


def add_analyze(sub) -> None:
    """analyze: give every supported branch a verdict."""
    p = sub.add_parser(
        "analyze", help="give an affected / not affected verdict for every branch"
    )
    p.add_argument(
        "--commit",
        help=f"{_COMMIT_HELP} (default: your branch's commits since origin/main)",
    )
    p.add_argument(
        "--yes",
        action="store_true",
        help="skip the interactive test-file confirmation (for scripted/CI runs)",
    )
    p.add_argument("--branches", nargs="+", help="limit to these branches")
    p.add_argument("--json", action="store_true", help="emit JSON")
    add_common(p)
    p.set_defaults(func=cmd_analyze)


def add_apply(sub) -> None:
    """apply: cherry-pick onto local branches for review."""
    p = sub.add_parser("apply", help="cherry-pick the fix onto local branches")
    p.add_argument("--branches", nargs="+", help="branches to apply to")
    p.add_argument(
        "--all-affected", action="store_true", help="apply to every AFFECTED branch"
    )
    p.add_argument("--commit", help=f"{_COMMIT_HELP} (default: the last analyzed run)")
    p.add_argument("--yes", action="store_true", help="skip the confirmation prompt")
    add_common(p)
    p.set_defaults(func=cmd_apply)


def add_publish(sub) -> None:
    """publish: open a backport PR per affected branch (what CI runs)."""
    p = sub.add_parser(
        "publish",
        help="open backport PRs on the fork for a merged commit (what CI runs)",
    )
    p.add_argument("--commit", required=True, help="merged commit SHA to back-port")
    p.add_argument("--pr", help="source PR number (for cross-linking / comments)")
    p.add_argument(
        "--remote",
        default="origin",
        help="fork remote to push branches / open PRs on (default origin)",
    )
    p.add_argument(
        "--dry-run",
        action="store_true",
        help="analyze and cherry-pick locally but do not push or open PRs",
    )
    add_common(p)
    p.set_defaults(func=cmd_publish, json=False)


def add_resolve(sub) -> None:
    """resolve: fix conflicting backports by hand, one branch at a time."""
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
    p.set_defaults(func=cmd_resolve, json=False)


def add_clear(sub) -> None:
    """clear: delete the saved run."""
    p = sub.add_parser(
        "clear",
        help="remove the saved run state (.backport-runs/) from the tool folder",
    )
    add_common(p)
    p.set_defaults(func=cmd_clear)


def build_parser() -> argparse.ArgumentParser:
    """Build the ``backport`` argument parser (analyze / apply / publish / clear)."""
    ap = argparse.ArgumentParser(
        prog="backport",
        description="Local AWS-LC backport impact analysis + apply.",
    )
    sub = ap.add_subparsers(dest="cmd", required=True)
    add_analyze(sub)
    add_apply(sub)
    add_publish(sub)
    add_resolve(sub)
    add_clear(sub)
    return ap


# --- Entrypoint -----------------------------------------------------------


def main(argv: Optional[Sequence[str]] = None) -> int:
    """Parse arguments, pick the checkout, and run the subcommand."""
    args = build_parser().parse_args(argv)
    try:
        target_repo(args)
        return args.func(args)
    except BackportError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
