"""Configurations for backport tool"""

import json
import os
import time
from functools import lru_cache
from pathlib import Path
from typing import Dict, List, Sequence

# _________ Verdict States & Error Catching _________
# Every branch ends up in exactly one of these
AFFECTED = "affected"
NOT_AFFECTED = "not_affected"
UNSURE = "unsure"
ALREADY = "already_patched"

# How each state prints in the table
LABEL = {
    AFFECTED: "AFFECTED",
    NOT_AFFECTED: "not affected",
    UNSURE: "UNSURE",
    ALREADY: "already patched",
}


class BackportError(Exception):
    """
    A problem to show the user
    'main' prints these as 'error: ...' and exits 1.
    Anything else stays a traceback
    """


# _________ LLM Settings _________
# Reads from model-config.json

# Hard limit guardrails for read and send to the model
MAX_DIFF_BYTES = 40000
MAX_FILE_BYTES = 45000

# Finds where ./util/backport is
TOOL_ROOT = Path(__file__).resolve().parent.parent.parent
SETTINGS_PATH = TOOL_ROOT / "model-config.json"
REQUIRED_CFG = ("model_id", "aws_region", "max_tokens")


@lru_cache(maxsize=1)
def load_model_config() -> dict:
    """
    Read model-config.json. Raises if missing or incomplete
    """
    try:
        cfg = json.loads(SETTINGS_PATH.read_text(encoding="utf-8"))
    except FileNotFoundError:
        raise BackportError(f"missing config file: {SETTINGS_PATH}")
    except json.JSONDecodeError as exc:
        raise BackportError(f"{SETTINGS_PATH} is not valid JSON: {exc}")

    missing = [k for k in REQUIRED_CFG if k not in cfg]
    if missing:
        raise BackportError(f"{SETTINGS_PATH} is missing: {', '.join(missing)}")
    return cfg


# _________ Analysis Tuning _________
# -- Which files count as a real source --
GENERATED_PATHSPECS = [
    p.strip()
    for p in os.environ.get("BACKPORT_GENERATED_PATHS", "generated-src").split(",")
    if p.strip()
]

TEST_SUFFIXES = ("_test.cc", "_test.cpp", "_test.c", "_test.cxx")


def fingerprint_pathspec() -> List[str]:
    """Paths to compare when fingerprinting, generated files left out"""
    if not GENERATED_PATHSPECS:
        return []
    return ["--", "."] + [f":(exclude){p}" for p in GENERATED_PATHSPECS]


def is_test_or_generated_file(f: str) -> bool:
    """
    Checks if file is a test or a generated file
    Omitted from analysis
    """
    if any(f == p or f.startswith(p.rstrip("/") + "/") for p in GENERATED_PATHSPECS):
        return True
    # Lowercased so the name checks behave like is_c_file, which also ignores case
    low = f.lower()
    base = low.rsplit("/", 1)[-1]
    return (
        "_test." in base
        or base.startswith("test_")
        or low.startswith("test/")
        or "/test/" in low
        or "fuzz" in low
    )


# -- Which branches count as releases --
# Matches release branches by name prefix. Covers the real branches and the
# NetOS one, which has no date in its name
SUPPORTED_BRANCH_PREFIXES = tuple(
    p.strip()
    for p in os.environ.get(
        "BACKPORT_BRANCH_PREFIXES",
        "origin/fips-,origin/AWS-LC-FIPS-,origin/NetOS",
    ).split(",")
    if p.strip()
)

# A release branch's own commits are the ones it has that this ref does not
MAINLINE_REF = os.environ.get("BACKPORT_MAINLINE_REF", "origin/main")


# _________ The Saved Run _________
# analyze writes its result here so apply can pick it up. Kept next to the tool,
# never inside the repo being analyzed

RUN_FILE = TOOL_ROOT / ".backport-runs" / "last-run.json"


def save_run(
    fix: str, base: str, branches: Sequence[str], buckets: Dict[str, str]
) -> None:
    """Saves this analyze run for apply to read"""
    RUN_FILE.parent.mkdir(parents=True, exist_ok=True)
    RUN_FILE.write_text(
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
