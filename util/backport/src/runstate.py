"""
Run-state persistence.

Layer: persistence (leaf-ish). Builds on ``common`` only; the bridge between the
``analyze`` and ``apply`` commands.

``analyze`` saves its result (the fix commit, its base, the branch buckets) here so
a later ``apply`` can reuse it without re-analyzing. The state lives next to the
tool itself -- inside the ``util/backport`` folder -- so it never writes into the
target repo checkout.
"""

import json
import time
from pathlib import Path
from typing import Dict, Sequence

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
    fix: str,
    base: str,
    branches: Sequence[str],
    buckets: Dict[str, str],
) -> None:
    """Persist this analyze run so ``apply`` can pick up where it left off."""
    directory = run_dir()
    directory.mkdir(parents=True, exist_ok=True)
    run_file().write_text(
        json.dumps(
            {
                "generated_at": time.strftime("%Y-%m-%d %H:%M:%S"),
                "fix": fix,
                "base": base,
                "branches": list(branches),
                "buckets": buckets,
            },
            indent=2,
        )
    )


def load_run() -> dict:
    """Load the saved run, or raise if none exists."""
    path = run_file()
    if not path.exists():
        raise BackportError(
            "no saved run found. Run `backport analyze` first, or name the fix "
            "with --commit <ref>."
        )
    return json.loads(path.read_text())
