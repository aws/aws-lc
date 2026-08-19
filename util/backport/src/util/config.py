# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""Configurations for backport tool"""

import json
import os
import sys
import time
from calendar import monthrange
from datetime import date, datetime
from functools import lru_cache
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

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
# MAX_FILE_BYTES is a prompt budget: up to six files go into one question. It covers
# about 97% of aws-lc's sources, and anything larger is marked as cut off
MAX_DIFF_BYTES = 40000
MAX_FILE_BYTES = 100000

# Adaptive thinking spends this budget before the answer starts, so too small a value
# cuts the verdict off. Specific to this tool, so it stays out of the shared config
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
    branch in play, since an unreadable manifest must not shrink the list of branches a
    fix is checked against
    """
    try:
        listed = json.loads(VERSIONS_PATH.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError) as exc:
        print(
            f"warning: could not read {VERSIONS_PATH.name} ({exc}), so no branch will "
            "be dropped for being out of support",
            file=sys.stderr,
        )
        return {}
    entries = listed.get("fips_branches", [])
    return {e["branch"]: e for e in entries if e.get("branch")}


def support_end_date(value: Optional[str]) -> Optional[date]:
    """
    A YYYY-MM or YYYY-MM-DD end-of-support string as the last day still supported
    Returns None when there is nothing to parse, which callers read as no published
    end date, so still supported

    A bare month means supported through all of that month, which is how VERSIONING.md
    publishes it, so YYYY-MM becomes the last day of the month and not the first. Taking
    the first would drop a branch up to 30 days early, and an early drop is silent: the
    branch leaves the report rather than being reported as affected
    """
    for shape in ("%Y-%m-%d", "%Y-%m"):
        try:
            parsed = datetime.strptime((value or "").strip(), shape).date()
        except ValueError:
            continue
        if shape == "%Y-%m":
            return parsed.replace(day=monthrange(parsed.year, parsed.month)[1])
        return parsed
    return None


def out_of_support(branch: str, today: Optional[date] = None) -> Optional[str]:
    """
    Why a branch is out of support, or None when it still is supported
    A branch missing from the manifest counts as supported: unknown must not mean
    silently skipped, since the cost of that is a missed backport. The published end
    date is the last supported day, so a branch is only dropped after it has passed
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


# --- The FIPS Boundary ---
# The module is validated as a build of exactly this source, so touching it has
# certification consequences the tool cannot judge. It reports them for review
#
# util/fipstools is excluded, it drives the module from outside
FIPS_BOUNDARY_PATHS = ("crypto/fipsmodule/",)


def fips_boundary_files(files: Sequence[str]) -> Tuple[List[str], str]:
    """
    Which of the given files are inside the validated FIPS module, and what to say

    files: paths a fix changed, relative to the repository root
    Returns (inside, note): the files inside the module, and one line naming them for a
    human. Both are empty when the fix stays outside the module

    Matched on the path prefix, so new files under crypto/fipsmodule are covered. Tests
    and generated files are excluded, since neither is compiled into the module
    """
    inside = [
        f
        for f in files
        if f.startswith(FIPS_BOUNDARY_PATHS) and not is_test_or_generated_file(f)
    ]
    if not inside:
        return [], ""
    shown = ", ".join(inside[:3])
    if len(inside) > 3:
        shown += f", and {len(inside) - 3} more"
    return inside, (
        f"touches the validated FIPS module ({len(inside)} file(s): {shown}). "
        "A backport here has certification consequences: get FIPS review before merging"
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
    fix: str,
    base: str,
    branches: Sequence[str],
    verdicts: Dict[str, str],
    fips_files: Optional[Sequence[str]] = None,
) -> None:
    """
    Saves what analyze decided, for apply and publish to pick up

    The file it writes:
        generated_at  when this ran, shown by apply so a stale run is obvious
        fix           the commit being backported
        base          what the fix was compared against
        branches      every release branch that was looked at
        verdicts      one of the four verdicts per branch, the part apply acts on
        fips_files    the files inside the validated FIPS module, so publish can carry
                      the warning into every pull request it opens
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
                "fips_files": list(fips_files or []),
            },
            indent=2,
        ),
        encoding="utf-8",
    )
