"""
Tunable knobs, per-process caches, and model/branch configuration.

Layer: impact core (``engine`` package). Builds on ``settings``.
"""

import os

import settings

# ---------------------------------------------------------------------------
# 2. Caches, constants & configuration
# ---------------------------------------------------------------------------

_AI_MAX_DIFF_BYTES = settings.MAX_DIFF_BYTES  # cap diff bytes fed to the model
_AI_MAX_FILE_BYTES = (
    settings.MAX_FILE_BYTES
)  # cap per-file context bytes fed to the model

# Per-process caches for the pre-image work, which repeats identical git calls
# within one analysis. Keys are prefixed with the unique fix SHA, so entries
# never collide across fixes/sandboxes.
_REMOVED_LINES_CACHE: "dict[tuple, list]" = {}
_PREIMAGE_CACHE: "dict[tuple, object]" = {}


# Auto-generated/derived files (e.g. generated-src/). They are regenerated
# per-branch, so their bytes differ between a fix and its backport even when the
# real source change is identical -- including them in patch-id matching would
# flag an already-applied backport as novel. Overridable via env (comma-separated).
_GENERATED_PATHSPECS = [
    p.strip()
    for p in os.environ.get("BACKPORT_GENERATED_PATHS", "generated-src").split(",")
    if p.strip()
]


def patch_id_pathspec():
    """Git pathspec keeping every file except the generated ones, so a patch-id
    reflects only human-authored source. Returns [] when nothing is excluded."""
    if not _GENERATED_PATHSPECS:
        return []
    return ["--", "."] + [f":(exclude){p}" for p in _GENERATED_PATHSPECS]


# Bedrock model pin + AI knobs live in model-config.json (see settings.py).
_BEDROCK_MODEL_ID = settings.MODEL_ID

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
