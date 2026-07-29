"""
Rename-aware git file and diff reads.

Layer: impact core (``engine`` package). Builds on ``config``.
"""

import subprocess

from .config import _AI_MAX_DIFF_BYTES, _AI_MAX_FILE_BYTES

# ---------------------------------------------------------------------------
# 6. Git file access (rename-aware)
# ---------------------------------------------------------------------------


def get_commit_diff(commit):
    """Return the full diff for *commit* as a string (capped at _AI_MAX_DIFF_BYTES)."""
    result = subprocess.run(
        ["git", "show", "--stat", "-p", commit],
        capture_output=True,
        text=True,
        errors="replace",
    )
    if result.returncode != 0:
        return ""
    return result.stdout[:_AI_MAX_DIFF_BYTES]


def show_file(ref, path):
    """Raw contents of *path* at *ref*, or None if it doesn't exist there."""
    result = subprocess.run(
        ["git", "show", f"{ref}:{path}"],
        capture_output=True,
        text=True,
        errors="replace",
    )
    if result.returncode != 0:
        return None
    return result.stdout


def historical_paths(commit, file_path, limit=6):
    """Paths *file_path* has occupied over its history (current first, then older
    names, following renames) as of *commit* -- so we can find the file on a
    branch that forked before a rename."""
    paths = [file_path]
    result = subprocess.run(
        [
            "git",
            "log",
            "--follow",
            "--name-status",
            "--format=",
            commit,
            "--",
            file_path,
        ],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        return paths
    seen = {file_path}
    for line in result.stdout.splitlines():
        parts = line.split("\t")
        # Rename entries look like: R100<TAB>old/path<TAB>new/path
        if parts and parts[0].startswith("R") and len(parts) >= 3:
            old = parts[1].strip()
            if old and old not in seen:
                paths.append(old)
                seen.add(old)
                if len(paths) >= limit:
                    break
    return paths


def get_file_on_branch(file_path, branch_ref, commit=None):
    """(content, resolved_path) for *file_path* on *branch_ref*, capped at
    _AI_MAX_FILE_BYTES. If absent at the current path and *commit* is given,
    follows rename history to try earlier paths. (None, None) if not found."""
    content = show_file(branch_ref, file_path)
    if content is not None:
        return content[:_AI_MAX_FILE_BYTES], file_path
    if commit:
        for older in historical_paths(commit, file_path):
            if older == file_path:
                continue
            content = show_file(branch_ref, older)
            if content is not None:
                return content[:_AI_MAX_FILE_BYTES], older
    return None, None
