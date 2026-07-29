"""
Introducer tracing: which commit(s) wrote the lines a fix changes.

Layer: impact core (``engine`` package). Builds on ``textutil`` + ``preimage``.
"""

import re
import subprocess
import sys

from .preimage import is_test_or_generated_file
from .textutil import is_noise_line

# ---------------------------------------------------------------------------
# 7. Introducer tracing
# ---------------------------------------------------------------------------


def find_introducing_commit(commit, files):
    """Commit(s) that introduced the code the fix changes. For each touched line
    range, `git log -L --reverse` gives the oldest commit to write those lines
    (the introducer), falling back to `git blame -w -M -C`. Comment/blank/
    punctuation-only hunks are skipped so a stale comment can't trace to an
    ancient import. Returns a set of SHAs."""
    introducing = set()

    for file in files:
        # Test/generated files aren't the vulnerable source, and their introducer
        # would over-flag branches that lack the fixed module.
        if is_test_or_generated_file(file):
            continue
        result = subprocess.run(
            ["git", "diff", "-U0", f"{commit}^", commit, "--", file],
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            raise RuntimeError(f"git diff failed: {result.stderr}")

        # Parse each hunk with its changed lines so noise-only hunks can be skipped.
        hunks = []
        cur = None
        for line in result.stdout.splitlines():
            if line.startswith("@@"):
                match = re.match(r"^@@ -(\d+)(?:,(\d+))? ", line)
                cur = None
                if match:
                    cur = {
                        "start": int(match.group(1)),
                        "count": int(match.group(2)) if match.group(2) else 1,
                        "changed": [],
                    }
                    hunks.append(cur)
            elif (
                cur is not None
                and line
                and line[0] in "+-"
                and not line.startswith(("+++", "---"))
            ):
                cur["changed"].append(line[1:])

        for h in hunks:
            if h["changed"] and all(is_noise_line(c, file) for c in h["changed"]):
                continue  # comment/blank/punctuation-only change: not impact-relevant
            old_start, old_count = h["start"], h["count"]
            if old_count == 0:
                # Pure addition: inspect the line right after the insertion point.
                blame_start = old_start + 1
                blame_end = old_start + 1
            else:
                # Lines were removed/modified: inspect those exact lines.
                blame_start = old_start
                blame_end = old_start + old_count - 1

            origin_sha = find_line_origin(file, blame_start, blame_end, f"{commit}^")
            if origin_sha:
                introducing.add(origin_sha)

    return introducing


def find_line_origin(file, line_start, line_end, ref):
    """SHA of the oldest commit to touch lines [line_start, line_end] of *file* as
    of *ref* (via `git log -L --reverse`), falling back to `git blame -w -M -C`."""
    log_result = subprocess.run(
        [
            "git",
            "log",
            f"-L{line_start},{line_end}:{file}",
            "--format=%H",
            "--reverse",
            ref,
        ],
        capture_output=True,
        text=True,
    )
    if log_result.returncode == 0:
        for log_line in log_result.stdout.splitlines():
            log_line = log_line.strip()
            # `--format=%H` only prints SHAs on their own lines; the rest is the
            # diff body. Take the first 40-char hex string we see.
            if len(log_line) == 40 and all(c in "0123456789abcdef" for c in log_line):
                return log_line

    # Fallback: use blame (with whitespace/move-aware flags). Less accurate for
    # finding the original introducer, but works on edge cases log -L can't.
    blame_result = subprocess.run(
        [
            "git",
            "blame",
            "-w",
            "-M",
            "-C",
            "-L",
            f"{line_start},{line_end}",
            ref,
            "--",
            file,
        ],
        capture_output=True,
        text=True,
    )
    if blame_result.returncode != 0:
        # Both failed -- usually a pure addition whose post-insertion line is at/past
        # EOF in the parent (newly-added lines have no pre-image). Skip this hunk.
        print(
            f"[introducer] no pre-image for {file}:{line_start}-{line_end} on "
            f"{ref} (likely newly-added lines); skipping this hunk.",
            file=sys.stderr,
        )
        return None
    for blame_line in blame_result.stdout.splitlines():
        if not blame_line:
            continue
        return blame_line.split()[0].lstrip("^")
    return None
