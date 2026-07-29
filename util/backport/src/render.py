"""
Rendering the analyze result.

Layer: output. Builds on ``common`` only; used by ``analyze`` (and reused by
``ci`` / ``resolve``) to present verdicts. No git or analysis logic lives here.

Two output modes: a human-readable table (AFFECTED branches first, columns
auto-sized to the widest value) followed by a copy-paste backport hint, or a
single JSON object for scripting.
"""

import json
from typing import Dict, Sequence

from common import AFFECTED, ALREADY, LABEL, NOT_AFFECTED, UNSURE


def print_summary(
    fix_sha: str,
    files: Sequence[str],
    introducers: Sequence[str],
    buckets: Dict[str, str],
    decided_by: Dict[str, str],
) -> None:
    """Print the per-branch verdict table."""
    print(f"Fix commit (built from patch): {fix_sha[:10]}")
    print(f"Changed files: {list(files)}")
    print(f"Introducer(s): {[s[:8] for s in introducers] or '(none / new file)'}")
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
    as_json, fix_sha, base, files, introducers, buckets, decided_by, summaries
) -> None:
    """Print the analysis result, as JSON or as the human-readable table + hint."""
    if as_json:
        print(
            json.dumps(
                {
                    "fix_commit": fix_sha,
                    "base": base,
                    "changed_files": files,
                    "introducers": introducers,
                    "buckets": buckets,
                    "decided_by": decided_by,
                    "summaries": summaries,
                },
                indent=2,
            )
        )
    else:
        print_summary(fix_sha, files, introducers, buckets, decided_by)
        print_backport_hint(buckets)
