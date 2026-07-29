"""
Vulnerable pre-image: are the lines the fix removes still present on a branch?

Layer: impact core (``engine`` package). Builds on ``config`` + ``textutil``.
"""

import re
import subprocess

from .config import _GENERATED_PATHSPECS, _PREIMAGE_CACHE, _REMOVED_LINES_CACHE
from .textutil import is_boilerplate_line, is_noise_line, norm_ws

# ---------------------------------------------------------------------------
# 5. Vulnerable pre-image (are the fix's removed lines still on a branch?)
# ---------------------------------------------------------------------------


def fix_removed_lines(commit, file):
    """The distinctive lines the fix removes/changes for *file* (the vulnerable
    pre-image), skipping comments, blanks, punctuation, and boilerplate."""
    cache_key = (commit, file)
    if cache_key in _REMOVED_LINES_CACHE:
        return _REMOVED_LINES_CACHE[cache_key]
    diff = subprocess.run(
        ["git", "diff", f"{commit}^", commit, "--", file],
        capture_output=True,
        text=True,
    )
    if diff.returncode != 0:
        _REMOVED_LINES_CACHE[cache_key] = []
        return []
    removed = []
    for line in diff.stdout.splitlines():
        if line.startswith("-") and not line.startswith("---"):
            s = line[1:].strip()
            if is_noise_line(s, file):
                continue
            if is_boilerplate_line(s):
                continue
            if len(re.sub(r"\W", "", s)) >= 6:  # enough alnum to be distinctive
                removed.append(s)
    _REMOVED_LINES_CACHE[cache_key] = removed
    return removed


def vulnerable_preimage_present(commit, changed_files, ref):
    """Whether the exact lines the fix removes/changes are still on *ref*:
    True  -> present (branch still vulnerable);
    False -> provably absent (code diverged or not here);
    None  -> the fix removes nothing distinctive (pure addition), can't tell.
    """
    cache_key = (commit, tuple(changed_files), ref)
    if cache_key in _PREIMAGE_CACHE:
        return _PREIMAGE_CACHE[cache_key]
    result = vulnerable_preimage_present_uncached(commit, changed_files, ref)
    _PREIMAGE_CACHE[cache_key] = result
    return result


def is_test_or_generated_file(f):
    """True for test or auto-generated files. Their content is not the shipped
    vulnerable source, so a pre-image match there is not evidence of impact."""
    if any(f == p or f.startswith(p.rstrip("/") + "/") for p in _GENERATED_PATHSPECS):
        return True
    base = f.rsplit("/", 1)[-1]
    return (
        "_test." in base
        or base.startswith("test_")
        or f.startswith("test/")
        or "/test/" in f
        or "fuzz" in f
    )


def vulnerable_preimage_present_uncached(commit, changed_files, ref):
    saw_removed = False
    for file in changed_files:
        # Skip test/generated files: a match there isn't the shipped vulnerable
        # code, and counting it produced false 'still present' (affected) results.
        if is_test_or_generated_file(file):
            continue
        removed = fix_removed_lines(commit, file)
        if not removed:
            continue
        saw_removed = True
        show = subprocess.run(
            ["git", "show", f"{ref}:{file}"], capture_output=True, text=True
        )
        if show.returncode != 0:
            continue
        content = norm_ws(show.stdout)
        for rl in removed:
            if norm_ws(rl) in content:
                return True
    if not saw_removed:
        return None
    return False
