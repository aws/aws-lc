# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""
Prints the analyze result and asks the yes/no questions
No git or analysis logic here
"""

from util.config import AFFECTED, ALREADY, LABEL, NOT_AFFECTED, TEST_SUFFIXES, UNSURE

from typing import Dict, Sequence

# Affected first, those are the ones to act on
ORDER = {AFFECTED: 0, UNSURE: 1, ALREADY: 2, NOT_AFFECTED: 3}


def print_summary(
    fix_sha: str,
    files: Sequence[str],
    bug_commits: Sequence[str],
    buckets: Dict[str, str],
    decided_by: Dict[str, str],
) -> None:
    """Prints every branch and its verdict as a table"""
    print(f"Fix commit: {fix_sha[:10]}")
    print(f"Changed files: {list(files)}")
    print(f"Wrote these lines: {[s[:8] for s in bug_commits] or '(none / new file)'}")
    print()

    # Widths follow the longest value so long branch names stay lined up
    branch_w = max([len("branch")] + [len(b) for b in buckets])
    status_w = max([len("status")] + [len(LABEL[s]) for s in buckets.values()])
    print(f"  {'branch':<{branch_w}} {'status':<{status_w}} basis")
    print(f"  {'-' * branch_w} {'-' * status_w} {'-' * 40}")

    # sorted() is stable, so branches stay newest first inside each group
    for branch, state in sorted(buckets.items(), key=lambda kv: ORDER.get(kv[1], 9)):
        basis = decided_by.get(branch, "")
        print(f"  {branch:<{branch_w}} {LABEL[state]:<{status_w}} {basis}".rstrip())


def ask_yn(prompt: str) -> bool:
    """Asks until the answer is Y or N. True for Y"""
    while True:
        try:
            answer = input(f"{prompt} [Y/N] ").strip().lower()
        except EOFError:
            return False  # nothing to read, treat as no
        if answer in ("y", "yes"):
            return True
        if answer in ("n", "no"):
            return False
        print("Please answer Y or N.")


def confirm_test_file(changed_files) -> bool:
    """
    Checks the fix ships a test before the slow work starts
    True keeps going, N aborts
    """
    tests = sorted(f for f in changed_files if f.endswith(TEST_SUFFIXES))
    if tests:
        print(f"Test file in this fix: {', '.join(tests)}")
        return ask_yn("Is this the test for your fix?")
    print("No test file (e.g. *_test.cc) found in this fix.")
    return ask_yn("Proceed without a test file?")
