"""
Rendering the analyze result.

Layer: output. Builds on ``util.config`` only; used by the commands to present
verdicts and prompt the user. No git or analysis logic lives here.

Two output modes: a human-readable table (AFFECTED branches first, columns
auto-sized to the widest value) followed by a copy-paste backport hint, or a
single JSON object for scripting.
"""

import json
from typing import Dict, Sequence

from util.config import AFFECTED, ALREADY, LABEL, NOT_AFFECTED, TEST_SUFFIXES, UNSURE


def print_summary(
    fix_sha: str,
    files: Sequence[str],
    bug_commits: Sequence[str],
    buckets: Dict[str, str],
    decided_by: Dict[str, str],
) -> None:
    """Print the per-branch verdict table."""
    print(f"Fix commit: {fix_sha[:10]}")
    print(f"Changed files: {list(files)}")
    print(f"Wrote these lines: {[s[:8] for s in bug_commits] or '(none / new file)'}")
    print()
    # Size the branch/status columns to the widest value so long names (e.g. a
    # "-snapshot" branch) never break the alignment.
    bw = max([len("branch")] + [len(b) for b in buckets])
    sw = max([len("status")] + [len(LABEL[s]) for s in buckets.values()])
    print(f"  {'branch':<{bw}} {'status':<{sw}} basis")
    print(f"  {'-' * bw} {'-' * sw} {'-' * 40}")
    # Show AFFECTED first (the actionable branches), then the rest; buckets are
    # already newest-first, and the sort is stable, so each group keeps that order.
    order = {AFFECTED: 0, UNSURE: 1, ALREADY: 2, NOT_AFFECTED: 3}
    for branch, state in sorted(buckets.items(), key=lambda kv: order.get(kv[1], 9)):
        print(f"  {branch:<{bw}} {LABEL[state]:<{sw}} {decided_by.get(branch, '')}")


def print_backport_hint(buckets: Dict[str, str]) -> None:
    """After the verdict table, tell the user how to backport the AFFECTED branches.
    The last analyze run is saved, so ``apply`` reuses it without re-passing the fix."""
    affected = [b for b, s in buckets.items() if s == AFFECTED]
    if not affected:
        return
    print("\nTo cherry-pick onto local backport branches (nothing is pushed), run:")
    print("  ./backport apply --all-affected")
    print("or target specific branches, e.g.:")
    print(f"  ./backport apply --branches {' '.join(affected)}")


def emit_analysis(
    as_json, fix_sha, base, files, bug_commits, buckets, decided_by, summaries
) -> None:
    """Print the analysis result, as JSON or as the human-readable table + hint."""
    if as_json:
        print(
            json.dumps(
                {
                    "fix_commit": fix_sha,
                    "base": base,
                    "changed_files": files,
                    "bug_commits": bug_commits,
                    "buckets": buckets,
                    "decided_by": decided_by,
                    "summaries": summaries,
                },
                indent=2,
            )
        )
    else:
        print_summary(fix_sha, files, bug_commits, buckets, decided_by)
        print_backport_hint(buckets)


def print_section(title, items) -> None:
    """One titled, indented block of a run summary (``apply`` / ``resolve``)."""
    print(f"  {title}:")
    for item in items:
        print(f"    - {item}")
    print()


def ask_yn(prompt: str) -> bool:
    """Prompt until the user answers Y or N. Returns True for Y."""
    while True:
        try:
            ans = input(f"{prompt} [Y/N] ").strip().lower()
        except EOFError:
            # no input available (e.g. stdin closed) -> treat as a safe abort
            return False
        if ans in ("y", "yes"):
            return True
        if ans in ("n", "no"):
            return False
        print("Please answer Y or N.")


def confirm_test_file(changed_files) -> bool:
    """Confirm the fix ships a test before analysing it. Returns True to proceed.

    AWS-LC fixes usually carry their test alongside as a ``*_test.cc``. If one is
    present, confirm it is the right test; if none is, confirm the user wants to
    proceed anyway. Answering N aborts.
    """
    tests = sorted(f for f in changed_files if f.endswith(TEST_SUFFIXES))
    if tests:
        print(f"Test file in this fix: {', '.join(tests)}")
        return ask_yn("Is this the test for your fix?")
    print("No test file (e.g. *_test.cc) found in this fix.")
    return ask_yn("Proceed without a test file?")
