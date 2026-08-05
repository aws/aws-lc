# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""Configurations for backport tool"""

import json
import os
import time
from datetime import date, datetime
from functools import lru_cache
from pathlib import Path
from typing import Dict, List, Optional, Sequence

# --- Verdict States & Error Catching ---
# Every branch ends up in exactly one of these
AFFECTED = "affected"
NOT_AFFECTED = "not_affected"
UNSURE = "unsure"
ALREADY_PATCHED = "already_patched"

# How each state prints in the table
LABEL = {
    AFFECTED: "AFFECTED",
    NOT_AFFECTED: "not affected",
    UNSURE: "UNSURE",
    ALREADY_PATCHED: "already patched",
}


class BackportError(Exception):
    """
    A problem to show the user
    'main' prints these as 'error: ...' and exits 1.
    Anything else stays a traceback
    """


# --- LLM Settings ---
# Reads .github/workflows/ai-config.json, shared with the autofix workflow

# How much the tool will read and send to the model
# MAX_FILE_BYTES is a prompt budget, not a file size: up to six files go into one
# question, so this is what fits alongside the rest of the prompt. It covers all but
# about 3% of aws-lc's sources, and anything over it is marked as cut off rather than
# quietly shortened
MAX_DIFF_BYTES = 40000
MAX_FILE_BYTES = 100000

# What the model may spend on one reply. Generous on purpose: adaptive thinking spends
# this before the answer starts, so a tight budget cuts off the verdict lines and every
# branch comes back uncertain. It tunes this tool rather than naming the model, so it
# stays here and out of the shared config
MAX_ANSWER_TOKENS = 4096

# Finds where ./util/backport is
TOOL_ROOT = Path(__file__).resolve().parent.parent.parent

# The model id and region come from the repo's shared AI config, so this tool and the
# autofix workflow cannot drift onto different models. Two levels up from the tool is
# the checkout it lives in
SETTINGS_PATH = TOOL_ROOT.parent.parent / ".github" / "workflows" / "ai-config.json"
REQUIRED_CFG = ("aws_region", "opus")

# Which release branches are still in support, from VERSIONING.md
VERSIONS_PATH = TOOL_ROOT / "fips_versions.aws-lc.json"


@lru_cache(maxsize=1)
def load_model_config() -> dict:
    """
    Read the shared ai-config.json. Raises if missing or incomplete
    Returns the parsed config
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


@lru_cache(maxsize=1)
def load_supported_versions() -> Dict[str, dict]:
    """
    The support window for each release branch, keyed by branch name
    Returns an empty dict when the file is missing or unreadable, which leaves every
    branch in play. A manifest that cannot be read must not quietly shrink the list of
    branches a fix is checked against
    """
    try:
        listed = json.loads(VERSIONS_PATH.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        return {}
    entries = listed.get("fips_branches", [])
    return {e["branch"]: e for e in entries if e.get("branch")}


def support_end_date(value: Optional[str]) -> Optional[date]:
    """
    A YYYY-MM or YYYY-MM-DD end-of-support string as a date
    Returns None when there is nothing to parse, which callers read as no published
    end date, so still supported
    """
    for shape in ("%Y-%m-%d", "%Y-%m"):
        try:
            return datetime.strptime((value or "").strip(), shape).date()
        except ValueError:
            continue
    return None


def out_of_support(branch: str, today: Optional[date] = None) -> Optional[str]:
    """
    Why a branch is out of support, or None when it still is supported
    A branch missing from the manifest counts as supported: unknown must not mean
    silently skipped, since the cost of that is a missed backport
    """
    entry = load_supported_versions().get(branch)
    if entry is None:
        return None
    if not entry.get("actively_maintained", True):
        return "no longer actively maintained"
    ends = support_end_date(entry.get("end_of_support"))
    if ends is not None and ends < (today or date.today()):
        return f"support ended {entry.get('end_of_support')}"
    return None


# --- Analysis Tuning ---
# -- Which files count as a real source --
# Machine-written code, so a change there is a rebuild artifact, not a fix
GENERATED_PATHSPECS = ["generated-src"]

TEST_SUFFIXES = ("_test.cc", "_test.cpp", "_test.c", "_test.cxx")


def fingerprint_pathspec() -> List[str]:
    """Paths to compare when fingerprinting, generated files left out"""
    return ["--", "."] + [f":(exclude){p}" for p in GENERATED_PATHSPECS]


def is_test_or_generated_file(f: str) -> bool:
    """
    Checks if file is a test or a generated file
    Omitted from analysis
    True for either
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
# Matches release branches by name prefix, without a remote. Covers the real branches
# and the NetOS one, which has no date in its name
SUPPORTED_BRANCH_PREFIXES = ("fips-", "AWS-LC-FIPS-", "NetOS")

# Which remote the release branches are read from. Unset means work it out: the one
# pointing at aws/aws-lc when there is one, else origin. A fork is often behind on the
# release branches, or missing them entirely, so guessing origin is not safe
RELEASE_REMOTE = os.environ.get("BACKPORT_REMOTE", "").strip()


# --- The Saved Run ---
# analyze writes its result here so apply can pick it up. Kept next to the tool,
# never inside the repo being analyzed

RUN_FILE = TOOL_ROOT / ".backport-runs" / "last-run.json"


def save_run(
    fix: str, base: str, branches: Sequence[str], verdicts: Dict[str, str]
) -> None:
    """
    Saves what analyze decided, for apply to pick up

    The file it writes:
        generated_at  when this ran, shown by apply so a stale run is obvious
        fix           the commit being backported
        base          what the fix was compared against
        branches      every release branch that was looked at
        verdicts      one of the four verdicts per branch, the part apply acts on
    """
    RUN_FILE.parent.mkdir(parents=True, exist_ok=True)
    RUN_FILE.write_text(
        json.dumps(
            {
                "generated_at": time.strftime("%Y-%m-%d %H:%M:%S"),
                "fix": fix,
                "base": base,
                "branches": list(branches),
                "verdicts": verdicts,
            },
            indent=2,
        )
    )
