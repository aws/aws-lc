# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""
The analyze command: gives every supported release branch a verdict
"""

from engine.classify_branches import classify_branch
from engine.consult_ai import refine_with_ai
from engine.discover_branches import get_supported_branches
from engine.inspect_fix import find_bug_commits, only_source_files
from util.config import save_run
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

    branches = get_supported_branches()
    if not branches:
        print(
            "No supported branches found. Is this an AWS-LC clone with the "
            "release branches fetched (git fetch origin)?",
            file=sys.stderr,
        )
        return 1

    bug_commits = sorted(find_bug_commits(fix_sha, traceable_files))
    src_files = only_source_files(files)
    buckets = {
        branch: classify_branch(fix_sha, src_files, bug_commits, branch)
        for branch in branches
    }
    buckets, decided_by = refine_with_ai(fix_sha, src_files, bug_commits, buckets)

    print_summary(fix_sha, files, bug_commits, buckets, decided_by)
    save_run(fix_sha, base, branches, buckets)
    return 0
