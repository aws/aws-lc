"""
The ``analyze`` command.

Layer: command. Orchestrates ``patches`` -> ``verdicts`` -> ``render`` ->
``runstate``; wired into the CLI by ``main``.

Give every supported branch a definite verdict for a fix. Pipeline: read the
patch -> confirm the test file -> bucket each branch deterministically -> let the
AI decide the inconclusive ones -> print -> save the run -> delete the patch file.
"""

import os
import sys

import engine as bot
from patches import commit_from_patch, confirm_test_file, is_empty_patch, read_patch
from render import emit_analysis
from runstate import save_run
from verdicts import analyze_branches, resolve_inconclusive


def delete_analyze_patch(args) -> None:
    """Delete the source patch file once analysis is done (unless --keep-patch).

    The diff is still cached in the run file for a later ``apply``. Nothing to do
    when the diff was captured from the working tree (no file).
    """
    if args.patch and not args.keep_patch:
        try:
            os.remove(args.patch)
            print(f"\nDeleted patch file: {args.patch}")
        except OSError:
            pass


def cmd_analyze(args) -> int:
    """Give an affected / not affected verdict for every supported branch."""
    patch, base, from_file = read_patch(args)

    if is_empty_patch(patch):
        if from_file:
            print("patch is empty; nothing to analyze.")
        else:
            print(
                "No uncommitted changes to analyze (git diff HEAD is empty). "
                "Make your fix in the repo first, `git add` any new files, or "
                "pass a patch file."
            )
        return 0

    if not args.yes and not confirm_test_file(patch):
        print("Aborted. Re-run when your patch is ready.")
        return 0

    branches = bot.sort_branches(args.branches or bot.get_supported_branches())
    if not branches:
        print(
            "No supported branches found. Is this an AWS-LC clone with the "
            "release branches fetched (git fetch origin)?",
            file=sys.stderr,
        )
        return 1

    with commit_from_patch(patch, base, three_way=args.three_way) as fix_sha:
        files, introducers, buckets = analyze_branches(fix_sha, branches)
        buckets, decided_by, summaries = resolve_inconclusive(
            args, fix_sha, files, introducers, buckets
        )
        emit_analysis(
            args.json, fix_sha, base, files, introducers, buckets, decided_by, summaries
        )

    save_run(patch, base, branches, buckets, patch_path=args.patch)
    delete_analyze_patch(args)
    return 0
