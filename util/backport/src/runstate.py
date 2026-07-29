"""
Run-state persistence.

Layer: persistence (leaf-ish). Builds on ``common`` only; the bridge between the
``analyze`` and ``apply`` commands.

``analyze`` saves its result (the patch text, base ref, branch buckets) here so a
later ``apply`` can reuse it without re-reading the patch. The state lives next to
the tool itself -- inside the ``util/backport`` folder -- so it never writes into
the target repo checkout.
"""

import json
import os
import time
from pathlib import Path
from typing import Dict, List, Optional, Sequence

from common import BackportError

_RUN_DIR_NAME = ".backport-runs"
_RUN_FILE_NAME = "last-run.json"


def run_dir() -> Path:
    """Directory holding the saved run.

    Kept at the tool root (the parent of ``src/``), not next to this module, so
    the cache sits beside the README rather than buried in the source folder.
    """
    return Path(__file__).resolve().parent.parent / _RUN_DIR_NAME


def run_file() -> Path:
    """Path to the single saved-run JSON file."""
    return run_dir() / _RUN_FILE_NAME


def save_run(
    patch: str,
    base: str,
    branches: Sequence[str],
    buckets: Dict[str, str],
    patch_path: Optional[str] = None,
) -> None:
    """Persist this analyze run for a later ``apply``.

    The diff is cached under the ``patch`` key; *patch_path* is the source file
    (if any) so ``apply`` can delete it on a clean run.
    """
    directory = run_dir()
    directory.mkdir(parents=True, exist_ok=True)
    run_file().write_text(
        json.dumps(
            {
                "generated_at": time.strftime("%Y-%m-%d %H:%M:%S"),
                "base": base,
                "branches": list(branches),
                "buckets": buckets,
                "patch": patch,
                "patch_path": patch_path,
            },
            indent=2,
        )
    )


def load_run() -> dict:
    """Load the saved run, or raise if none exists."""
    path = run_file()
    if not path.exists():
        raise BackportError(
            "no saved run found. Run `backport analyze <patch>` first, "
            "or pass --patch <file>."
        )
    return json.loads(path.read_text())


def delete_patch_artifacts(patch_path: Optional[str]) -> List[str]:
    """Remove the source patch file and the saved run state (which embeds the
    patch text).

    Called after a clean apply so an embargoed diff does not linger on disk once
    the backport branches exist. Returns the list of paths removed.
    """
    removed: List[str] = []
    if patch_path and os.path.isfile(patch_path):
        try:
            os.remove(patch_path)
            removed.append(patch_path)
        except OSError:
            pass
    path = run_file()
    if path.exists():
        try:
            path.unlink()
            removed.append(str(path))
        except OSError:
            pass
    # Drop the now-empty run directory so nothing lingers in the checkout.
    directory = run_dir()
    if directory.is_dir() and not any(directory.iterdir()):
        try:
            directory.rmdir()
            removed.append(str(directory))
        except OSError:
            pass
    return removed
