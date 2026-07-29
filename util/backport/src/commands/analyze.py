"""
The ``analyze`` command.

Layer: command. Orchestrates ``util.git`` -> ``engine`` -> ``util.render`` ->
``util.config``; wired into the CLI by ``main``.

Give every supported branch a definite verdict for a fix. Pipeline: work out which
commit(s) the fix is -> confirm the test file -> bucket each branch
deterministically -> let the AI decide the inconclusive ones -> print -> save the
run so ``apply`` can reuse it.
"""

import sys

from engine.analysis import get_supported_branches, sort_branches
from util.git import changed_files_with_status, resolve_fix_commit
from util.render import confirm_test_file, emit_analysis
from util.config import save_run
from engine.ai import resolve_inconclusive
from engine.analysis import analyze_branches


def cmd_analyze(args) -> int:
    """Give an affected / not affected verdict for every supported branch."""
    fix_sha, base = resolve_fix_commit(args)

    # Confirm the test before the (slower) per-branch analysis, so an unfinished
    # fix is caught straight away.
    if not args.yes and not confirm_test_file(changed_files_with_status(fix_sha)[0]):
        print("Aborted. Re-run when your fix is ready.")
        return 0

    branches = sort_branches(args.branches or get_supported_branches())
    if not branches:
        print(
            "No supported branches found. Is this an AWS-LC clone with the "
            "release branches fetched (git fetch origin)?",
            file=sys.stderr,
        )
        return 1

    files, introducers, buckets = analyze_branches(fix_sha, branches)
    buckets, decided_by, summaries = resolve_inconclusive(
        args, fix_sha, files, introducers, buckets
    )
    emit_analysis(
        args.json, fix_sha, base, files, introducers, buckets, decided_by, summaries
    )
    save_run(fix_sha, base, branches, buckets)
    return 0
