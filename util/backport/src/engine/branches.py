"""
Supported-branch resolution: which release branches to consider, and their order.

Layer: impact core (``engine`` package). Builds on ``config``.
"""

import json
import os
import re
import subprocess
import sys
from datetime import date, datetime

from .config import SUPPORTED_BRANCH_PREFIXES, VERSIONS_MANIFEST_PATH

# ---------------------------------------------------------------------------
# 3. Supported-branch resolution
# ---------------------------------------------------------------------------


def remote_branch_names():
    """Branch names (without the `origin/` prefix) from `git branch -r`,
    skipping the symbolic `origin/HEAD -> origin/main` ref."""
    result = subprocess.run(["git", "branch", "-r"], capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"git branch -r failed: {result.stderr}")
    names = []
    for line in result.stdout.splitlines():
        line = line.strip()
        if " -> " in line or not line.startswith("origin/"):
            continue
        names.append(line[len("origin/") :])
    return names


def load_versions_manifest():
    """Load the FIPS branch manifest (`VERSIONS_MANIFEST_PATH`), or None if absent.

    Looks in the working tree first, then at the file as it exists on the mainline
    ref (so it still works from a feature branch). A present-but-malformed file
    logs a warning and returns None so we fall back to prefix matching.
    """
    text = None
    on_disk = os.path.join(os.getcwd(), VERSIONS_MANIFEST_PATH)
    if os.path.isfile(on_disk):
        try:
            with open(on_disk, encoding="utf-8") as fh:
                text = fh.read()
        except OSError:
            text = None
    if text is None:
        mainline = os.environ.get("BACKPORT_MAINLINE_REF", "origin/main")
        show = subprocess.run(
            ["git", "show", f"{mainline}:{VERSIONS_MANIFEST_PATH}"],
            capture_output=True,
            text=True,
        )
        if show.returncode == 0:
            text = show.stdout
    if not text or not text.strip():
        return None
    try:
        return json.loads(text)
    except json.JSONDecodeError as exc:
        print(
            f"[versions] {VERSIONS_MANIFEST_PATH} is present but not valid JSON "
            f"({exc}); falling back to branch-prefix matching.",
            file=sys.stderr,
        )
        return None


def parse_eos_date(value):
    """Parse an end-of-support date (`YYYY-MM-DD` or `YYYY-MM`). Returns None if
    missing/unparseable, which callers treat as "no known EOS" (still supported)."""
    for fmt in ("%Y-%m-%d", "%Y-%m"):
        try:
            return datetime.strptime((value or "").strip(), fmt).date()
        except ValueError:
            continue
    return None


def branch_support_status(today=None):
    """Per-branch support records derived from the manifest.

    Each record is the manifest entry plus `end_of_support_date`, `exists`
    (present as an origin/ ref), and `supported` (exists AND actively_maintained
    AND not past end_of_support as of `today`). Returns [] when no manifest.

    `today` is overridable so a historical replay can ask "was this branch in
    support as of the fix date?" rather than only "is it in support now?".
    """
    manifest = load_versions_manifest()
    if not manifest:
        return []
    today = today or date.today()
    remote = set(remote_branch_names())
    records = []
    for entry in manifest.get("fips_branches", []):
        name = entry.get("branch")
        if not name:
            continue
        eos = parse_eos_date(entry.get("end_of_support"))
        within_window = eos is None or eos >= today
        maintained = entry.get("actively_maintained", True)
        record = dict(entry)
        record["end_of_support_date"] = eos.isoformat() if eos else None
        record["exists"] = name in remote
        record["supported"] = bool(record["exists"] and maintained and within_window)
        records.append(record)
    return records


def branch_date_key(name):
    """The YYYY-MM-DD embedded in *name*, or '' if none. Used to order branches."""
    m = re.search(r"\d{4}-\d{2}-\d{2}", name)
    return m.group(0) if m else ""


def sort_branches(names):
    """Order branches newest -> oldest by the date in their name (undated last).
    The single source of truth for branch ordering, so every listing matches."""
    return sorted(
        names,
        key=lambda n: (branch_date_key(n) or "0000-00-00", n),
        reverse=True,
    )


def get_supported_branches(today=None):
    """Branch names (without `origin/`) to consider for backport, newest -> oldest.
    From the manifest when present (supported = exists as a ref, actively
    maintained, not past end-of-support), else branch-name prefix matching."""
    records = branch_support_status(today=today)
    if records:
        dropped = [r["branch"] for r in records if r["exists"] and not r["supported"]]
        if dropped:
            print(
                "[versions] skipping out-of-support branch(es) per "
                f"{VERSIONS_MANIFEST_PATH}: {', '.join(dropped)}",
                file=sys.stderr,
            )
        supported = [r["branch"] for r in records if r["supported"]]
    else:
        supported = [
            name
            for name in remote_branch_names()
            if f"origin/{name}".startswith(SUPPORTED_BRANCH_PREFIXES)
        ]
    return sort_branches(supported)


def get_changed_files(commit):
    """Files changed by the fix commit (vs. its parent)."""
    result = subprocess.run(
        ["git", "diff-tree", "--no-commit-id", "--name-only", "-r", commit],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        raise RuntimeError(f"git diff-tree failed: {result.stderr}")

    files = []

    for line in result.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        files.append(line)

    return files
