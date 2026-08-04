#!/usr/bin/env python3
"""
Main entry point for backport identification automation
Calls upon actions based on command-line arguments
"""

from commands.analyze import cmd_analyze
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


def build_parser() -> argparse.ArgumentParser:
    """
    Build parser for args
    """
    ap = argparse.ArgumentParser(
        prog="backport",
        description="Local CLI tool for backport analysis and automation",
    )
    subparsers = ap.add_subparsers(dest="cmd", required=True)
    add_analyze(subparsers)
    return ap


# ________ MAIN ________


def main(argv: Optional[Sequence[str]] = None) -> int:
    """
    Parses arguments and runs command
    """
    args = build_parser().parse_args(argv)

    try:
        return args.func(args)
    except BackportError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
