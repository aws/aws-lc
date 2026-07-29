"""
Shared vocabulary, tunable knobs, and saved run state.

Layer: foundation (leaf). Depends only on the standard library, so it can never
be part of an import cycle -- every other module may import it freely.

Four sections, all of them "things the rest of the tool needs to agree on":
  1. verdict states + the user-facing error type
  2. model / Bedrock settings, read from ``model-config.json``
  3. analysis knobs: per-process caches, generated-file pathspecs, branch
     discovery, and the test/generated-file predicate
  4. the saved run that bridges ``analyze`` -> ``apply``

The test/generated predicate lives here rather than with the analysis code
because it is a pure *path* question answered from configuration
(``_GENERATED_PATHSPECS``) -- and because ``util.git`` needs it too, which would
otherwise make analysis and git import each other.
"""

import json
import os
import time
from pathlib import Path

# --------------------------------------------------------------------------
# 1. Verdict states and errors
# --------------------------------------------------------------------------
#
# Every branch ends up in exactly one of these buckets. The deterministic engine
# only ever emits a confident NOT_AFFECTED when the changed code is provably
# absent; anything it cannot confirm becomes UNSURE and is handed to the AI layer
# (or, under --no-ai, flagged AFFECTED for review). So a real backport is never
# silently dropped.

AFFECTED = "affected"
NOT_AFFECTED = "not_affected"
UNSURE = "unsure"
ALREADY = "already_patched"

# Human-readable labels for the analyze table.
LABEL = {
    AFFECTED: "AFFECTED",
    NOT_AFFECTED: "not affected",
    UNSURE: "UNSURE",
    ALREADY: "already patched",
}


class BackportError(Exception):
    """A user-facing failure (bad ref, no saved run, cherry-pick failed, etc.).

    `main` catches this, prints it as a clean ``error: ...`` line, and exits 1 --
    as opposed to an unexpected exception, which surfaces its full traceback.
    """


# --------------------------------------------------------------------------
# 2. Model / Bedrock settings
# --------------------------------------------------------------------------
#
# All model pins and Bedrock call knobs live in one place -- ``model-config.json``
# at the tool root. Precedence for each value: environment variable >
# ``model-config.json`` > built-in default (so CI can override via env, and the
# tool still runs if the file is missing). To change the model, edit that file.

_DEFAULTS = {
    "model_id": "us.anthropic.claude-opus-4-8",
    "aws_region": "us-east-1",
    "max_tokens": 1024,
    "max_diff_bytes": 40000,
    "max_file_bytes": 45000,
}

# The tool root is two levels up from this module (src/util/config.py).
_TOOL_ROOT = Path(__file__).resolve().parent.parent.parent
_SETTINGS_PATH = _TOOL_ROOT / "model-config.json"


def load_model_config() -> dict:
    """Read ``model-config.json``, falling back to the built-in defaults."""
    cfg = dict(_DEFAULTS)
    try:
        loaded = json.loads(_SETTINGS_PATH.read_text(encoding="utf-8"))
        cfg.update({k: loaded[k] for k in _DEFAULTS if k in loaded})
    except (OSError, ValueError):
        pass  # keep defaults if the file is absent or malformed
    return cfg


_CFG = load_model_config()

MODEL_ID = os.environ.get("BEDROCK_MODEL_ID", _CFG["model_id"])
AWS_REGION = os.environ.get("AWS_REGION", _CFG["aws_region"])
MAX_TOKENS = int(os.environ.get("BEDROCK_MAX_TOKENS", _CFG["max_tokens"]))
# Caps on what we feed the model: whole-diff bytes, and per-file context bytes.
MAX_DIFF_BYTES = int(_CFG["max_diff_bytes"])
MAX_FILE_BYTES = int(_CFG["max_file_bytes"])


# --------------------------------------------------------------------------
# 3. Analysis knobs
# --------------------------------------------------------------------------

# Per-process caches for the pre-image work, which repeats identical git calls
# within one analysis. Keys are prefixed with the unique fix SHA, so entries
# never collide across fixes/sandboxes.
REMOVED_LINES_CACHE: "dict[tuple, list]" = {}
PREIMAGE_CACHE: "dict[tuple, object]" = {}

# Auto-generated/derived files (e.g. generated-src/). They are regenerated
# per-branch, so their bytes differ between a fix and its backport even when the
# real source change is identical -- including them in patch-id matching would
# flag an already-applied backport as novel. Overridable via env (comma-separated).
GENERATED_PATHSPECS = [
    p.strip()
    for p in os.environ.get("BACKPORT_GENERATED_PATHS", "generated-src").split(",")
    if p.strip()
]

# Prefixes matched against `origin/<branch>` when there is no manifest. Covers
# real release branches (fips-YYYY-MM-DD, fips-NetOS-*) and the POC fixture.
SUPPORTED_BRANCH_PREFIXES = tuple(
    p.strip()
    for p in os.environ.get(
        "BACKPORT_BRANCH_PREFIXES",
        "origin/fips-,origin/AWS-LC-FIPS-,origin/NetOS",
    ).split(",")
    if p.strip()
)

# FIPS/LTS branch manifest (kept in sync with VERSIONING.md). When present it is
# the source of truth for which branches are supported and their end-of-support;
# when absent we fall back to prefix matching.
VERSIONS_MANIFEST_PATH = os.environ.get(
    "BACKPORT_VERSIONS_MANIFEST", "fips_versions.json"
)

# The mainline a release branch's divergent commits are measured against.
MAINLINE_REF = os.environ.get("BACKPORT_MAINLINE_REF", "origin/main")

# Test-file suffixes, used both to spot a fix's own test and to exclude tests
# from impact analysis.
TEST_SUFFIXES = ("_test.cc", "_test.cpp", "_test.c", "_test.cxx")


def patch_id_pathspec():
    """Git pathspec keeping every file except the generated ones, so a patch-id
    reflects only human-authored source. Returns [] when nothing is excluded."""
    if not GENERATED_PATHSPECS:
        return []
    return ["--", "."] + [f":(exclude){p}" for p in GENERATED_PATHSPECS]


def is_test_or_generated_file(f):
    """True for test or auto-generated files. Their content is not the shipped
    vulnerable source, so a pre-image match there is not evidence of impact."""
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


# --------------------------------------------------------------------------
# 4. Saved run state (analyze -> apply)
# --------------------------------------------------------------------------
#
# `analyze` saves its result (the fix commit, its base, the branch buckets) so a
# later `apply` can reuse it without re-analyzing. The state lives next to the
# tool itself, so it never writes into the target repo checkout.

_RUN_DIR_NAME = ".backport-runs"
_RUN_FILE_NAME = "last-run.json"


def run_dir() -> Path:
    """Directory holding the saved run (at the tool root, beside the README)."""
    return _TOOL_ROOT / _RUN_DIR_NAME


def run_file() -> Path:
    """Path to the single saved-run JSON file."""
    return run_dir() / _RUN_FILE_NAME


def save_run(fix, base, branches, buckets) -> None:
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
