# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""
The analyze command: gives every supported release branch a verdict
"""

from engine.classify_branches import classify_branch
from engine.consult_ai import refine_with_ai
from engine.discover_branches import get_supported_branches
from engine.inspect_fix import find_bug_commits, only_source_files
from util.config import fips_boundary_files, fips_boundary_note, save_run
from util.git import changed_files_with_status, resolve_fix_commit
from util.render import confirm_test_file, print_summary

import sys


def cmd_analyze(args) -> int:
    """
    Works out the fix, then reports which branches still need it
    Returns the exit code: 0 when it ran or the user aborted, 1 when no supported
    branches were found
    """
    fix_sha, base = resolve_fix_commit(args)
    files, traceable_files = changed_files_with_status(fix_sha)

    # Asked before the slow part, so an unfinished fix is caught right away
    if not args.skip and not confirm_test_file(files):
        print("Aborted. Re-run when your fix is ready.")
        return 0

    branches, dropped = get_supported_branches()
    if dropped:
        # Said out loud, because a branch missing from the table below and a branch
        # that never needed the fix look identical to a reader
        for branch, why in dropped:
            print(f"Skipping {branch}: {why}", file=sys.stderr)
    if not branches:
        print(
            "No supported branches found. Is this an AWS-LC clone with the "
            "release branches fetched (git fetch origin)?",
            file=sys.stderr,
        )
        return 1

    bug_commits = sorted(find_bug_commits(fix_sha, traceable_files))
    src_files = only_source_files(files)
    verdicts = {
        branch: classify_branch(fix_sha, src_files, bug_commits, branch)
        for branch in branches
    }
    verdicts, decided_by = refine_with_ai(fix_sha, src_files, bug_commits, verdicts)

    print_summary(fix_sha, files, bug_commits, verdicts, decided_by)

    # Said after the table, where it is the last thing read. Every branch below is a
    # candidate for a change inside the validated module, so this is not per-branch news
    fips_files = fips_boundary_files(files)
    if fips_files:
        print()
        print(f"FIPS BOUNDARY: this fix {fips_boundary_note(fips_files)}.")

    save_run(fix_sha, base, branches, verdicts, decided_by, fips_files)
    return 0
