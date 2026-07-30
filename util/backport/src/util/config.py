"""
Shared constants, settings, and the saved run.

Nothing here imports anything else from the tool, so it can't cause import cycles.

  1. verdict states + the error type
  2. model settings, from model-config.json
  3. analysis knobs and the test/generated-file check
  4. the saved run that passes state from `analyze` to `apply`

The test/generated check lives here, not with the analysis code, because it only
looks at file paths -- and because util.git needs it too, which would otherwise
make analysis and git import each other.
"""

import json
import os
import time
from pathlib import Path
from typing import Dict, List, Sequence

# --- 1. Verdict states and errors -----------------------------------------

# Every branch ends up in exactly one of these. NOT_AFFECTED is only used when the
# code is provably absent; anything unclear becomes UNSURE and goes to the AI. If
# the AI can't answer, it becomes AFFECTED -- a needed backport is never dropped.

AFFECTED = "affected"
NOT_AFFECTED = "not_affected"
UNSURE = "unsure"
ALREADY = "already_patched"

# How each state prints in the analyze table.
LABEL = {
    AFFECTED: "AFFECTED",
    NOT_AFFECTED: "not affected",
    UNSURE: "UNSURE",
    ALREADY: "already patched",
}


class BackportError(Exception):
    """A problem to show the user (bad ref, no saved run, failed cherry-pick).

    `main` prints these as `error: ...` and exits 1. Anything else gets a
    traceback.
    """


# --- 2. Model settings ----------------------------------------------------

# Read from model-config.json at the tool root. Precedence: env var > that file >
# the defaults below. To change the model, edit the file.

_DEFAULTS = {
    "model_id": "us.anthropic.claude-opus-4-8",
    "aws_region": "us-east-1",
    "max_tokens": 1024,
    "max_diff_bytes": 40000,
    "max_file_bytes": 45000,
}

# Two levels up from src/util/config.py.
_TOOL_ROOT = Path(__file__).resolve().parent.parent.parent
_SETTINGS_PATH = _TOOL_ROOT / "model-config.json"


def load_model_config() -> dict:
    """Read model-config.json, or fall back to _DEFAULTS."""
    cfg = dict(_DEFAULTS)
    try:
        loaded = json.loads(_SETTINGS_PATH.read_text(encoding="utf-8"))
        cfg.update({k: loaded[k] for k in _DEFAULTS if k in loaded})
    except (OSError, ValueError):
        pass  # missing or malformed file -> defaults
    return cfg


_CFG = load_model_config()

MODEL_ID = os.environ.get("BEDROCK_MODEL_ID", _CFG["model_id"])
AWS_REGION = os.environ.get("AWS_REGION", _CFG["aws_region"])
MAX_TOKENS = int(os.environ.get("BEDROCK_MAX_TOKENS", _CFG["max_tokens"]))
# Size limits on what we send the model.
MAX_DIFF_BYTES = int(_CFG["max_diff_bytes"])
MAX_FILE_BYTES = int(_CFG["max_file_bytes"])


# --- 3. Analysis knobs ----------------------------------------------------

# One analysis repeats the same git calls a lot, so cache them. Keys start with the
# fix SHA, so entries never collide across fixes.
DELETED_LINES_CACHE: "dict[tuple, list]" = {}
STILL_PRESENT_CACHE: "dict[tuple, object]" = {}

# Machine-written files (generated-src/). Each branch generates its own copy, so
# the bytes can differ even when the human-written change is identical. Comparing
# them would make a backport look like a new change.
GENERATED_PATHSPECS = [
    p.strip()
    for p in os.environ.get("BACKPORT_GENERATED_PATHS", "generated-src").split(",")
    if p.strip()
]

# Used to find release branches when there's no manifest. Covers the real branches
# (fips-YYYY-MM-DD, fips-NetOS-*) and the POC fixture.
SUPPORTED_BRANCH_PREFIXES = tuple(
    p.strip()
    for p in os.environ.get(
        "BACKPORT_BRANCH_PREFIXES",
        "origin/fips-,origin/AWS-LC-FIPS-,origin/NetOS",
    ).split(",")
    if p.strip()
)

# Lists the supported branches and their end-of-support dates (kept in sync with
# VERSIONING.md). Used when present; otherwise we match the prefixes above.
VERSIONS_MANIFEST_PATH = os.environ.get(
    "BACKPORT_VERSIONS_MANIFEST", "fips_versions.json"
)

# A release branch's own commits are the ones it has that this ref doesn't.
MAINLINE_REF = os.environ.get("BACKPORT_MAINLINE_REF", "origin/main")

TEST_SUFFIXES = ("_test.cc", "_test.cpp", "_test.c", "_test.cxx")


def fingerprint_pathspec() -> List[str]:
    """Git pathspec that skips generated files, so a fingerprint covers only
    human-written code. Empty list if nothing is excluded."""
    if not GENERATED_PATHSPECS:
        return []
    return ["--", "."] + [f":(exclude){p}" for p in GENERATED_PATHSPECS]


def is_test_or_generated_file(f: str) -> bool:
    """True for test and machine-generated files. They aren't the shipped
    vulnerable code, so finding a match in one proves nothing."""
    if any(f == p or f.startswith(p.rstrip("/") + "/") for p in GENERATED_PATHSPECS):
        return True
    base = f.rsplit("/", 1)[-1]
    return (
        "_test." in base
        or base.startswith("test_")
        or f.startswith("test/")
        or "/test/" in f
        or "fuzz" in f
    )


# --- 4. The saved run (analyze -> apply) ----------------------------------

# `analyze` saves its result so `apply` can reuse it. Stored next to the tool, so
# we never write into the repo being analyzed.

_RUN_DIR_NAME = ".backport-runs"
_RUN_FILE_NAME = "last-run.json"


def run_dir() -> Path:
    """Where the saved run lives (tool root, next to the README)."""
    return _TOOL_ROOT / _RUN_DIR_NAME


def run_file() -> Path:
    """The saved-run JSON file."""
    return run_dir() / _RUN_FILE_NAME


def save_run(
    fix: str, base: str, branches: Sequence[str], buckets: Dict[str, str]
) -> None:
    """Save this analyze run for `apply` to pick up."""
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
    """Load the saved run, or raise if there isn't one."""
    path = run_file()
    if not path.exists():
        raise BackportError(
            "no saved run found. Run `backport analyze` first, or name the fix "
            "with --commit <ref>."
        )
    return json.loads(path.read_text())
