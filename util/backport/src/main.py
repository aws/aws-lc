#!/usr/bin/env python3
"""
backport - local CLI for the AWS-LC backport bot.

Layer: entrypoint. Wires the command modules (analyze / apply / publish /
resolve / clear) into one argument parser and dispatches to them.

Works on real commits: name a fix with ``--commit <ref>`` (or a range for a fix
split across several commits), or say nothing and it takes your current branch's
commits since it forked from the mainline -- so a fix can be assessed, and
backported to local branches, before it is merged. See README.md for what each
subcommand does; every flag is documented in its ``--help``.

Module map: util/ = config + git plumbing + output; engine/analysis = the
deterministic verdict; engine/ai = the advisory layer; commands/ = one module per
subcommand.
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


# --------------------------------------------------------------------------
# Argument parser
# --------------------------------------------------------------------------

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
    p.set_defaults(func=cmd_publish, json=False)


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
    p.set_defaults(func=cmd_resolve, json=False, no_ai=True)


def add_clear(sub) -> None:
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


# --------------------------------------------------------------------------
# Entrypoint
# --------------------------------------------------------------------------


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        target_repo(args)
        return args.func(args)
    except BackportError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
