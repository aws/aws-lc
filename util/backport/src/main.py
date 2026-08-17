#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
"""
Main entry point for backport identification automation
Calls upon actions based on command-line arguments
"""

from commands.analyze import cmd_analyze
from commands.apply import cmd_apply
from commands.publish import cmd_publish
from util.config import BackportError

import argparse
import sys
from typing import Optional, Sequence


def add_analyze(subparsers) -> None:
    """
    Determines each currently supported & affected branch
    By default, analyze takes your current branch's cumulative diff as input to analyze
    """
    p = subparsers.add_parser(
        "analyze", help="gives affected / not affected for each supported branch"
    )
    p.add_argument(
        "--commit", help="Allows you to specify which commits to analyze using SHAs"
    )
    p.add_argument(
        "--skip",
        action="store_true",
        help="Skips test file confirm. Useful for test scripts",
    )
    p.set_defaults(func=cmd_analyze)


def add_apply(subparsers) -> None:
    """
    Cherry-picks the analyzed fix onto a local branch per affected release branch
    Reads the run analyze saved, so analyze has to have run first
    """
    p = subparsers.add_parser(
        "apply", help="cherry-picks the fix onto a branch per affected branch"
    )
    p.add_argument(
        "--branch", help="only this release branch, instead of every affected one"
    )
    p.add_argument(
        "--yes",
        action="store_true",
        help="Skips the confirm. Useful for test scripts",
    )
    p.add_argument(
        "--open-pr",
        action="store_true",
        help="offer to open the pull requests once the cherry-picks are done",
    )
    p.add_argument(
        "--remote",
        default="origin",
        help="fork remote the branches are pushed to (default origin)",
    )
    p.set_defaults(func=cmd_apply)


def add_publish(subparsers) -> None:
    """
    Pushes the branches apply built and opens one pull request each
    Reads the same saved run, so analyze and apply have to have run first
    """
    p = subparsers.add_parser(
        "publish", help="opens a backport pull request for every affected branch"
    )
    p.add_argument("--branch", help="only this release branch")
    p.add_argument("--pr", help="source pull request number, to link and report on")
    p.add_argument(
        "--remote",
        default="origin",
        help="fork remote the branches are pushed to (default origin)",
    )
    p.add_argument(
        "--dry-run",
        action="store_true",
        help="say what would be pushed and opened, without doing it",
    )
    p.add_argument(
        "--push-to-aws-lc",
        action="store_true",
        help="let branches be pushed to aws/aws-lc. For CI, which runs there already",
    )
    p.add_argument(
        "--yes",
        action="store_true",
        help="Skips the confirm. Useful for test scripts",
    )
    p.set_defaults(func=cmd_publish)


def build_parser() -> argparse.ArgumentParser:
    """
    Build parser for args
    Returns the parser, with the analyze, apply and publish subcommands on it
    """
    ap = argparse.ArgumentParser(
        prog="backport",
        description="Local CLI tool for backport analysis and automation",
    )
    subparsers = ap.add_subparsers(dest="cmd", required=True)
    add_analyze(subparsers)
    add_apply(subparsers)
    add_publish(subparsers)
    return ap


# --- MAIN ---


def main(argv: Optional[Sequence[str]] = None) -> int:
    """
    Parses arguments and runs command
    Returns the command's exit code, or 1 when it raised a BackportError
    """
    args = build_parser().parse_args(argv)

    try:
        return args.func(args)
    except BackportError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
