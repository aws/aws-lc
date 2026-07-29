"""
Backport engine: the deterministic core (package).

Layer: impact core. Split into focused modules; this ``__init__`` re-exports the
full former ``engine`` API so existing imports (``import engine as bot``,
``from engine import ...``) keep working unchanged.

Modules: repo, config, branches, textutil, preimage, gitread, introducers, impact.
"""

from . import repo
from .repo import git_in_repo, run_in_repo, set_repo_path  # noqa: F401
from .config import (
    SUPPORTED_BRANCH_PREFIXES,
    VERSIONS_MANIFEST_PATH,
    _AI_MAX_DIFF_BYTES,
    _AI_MAX_FILE_BYTES,
    _BEDROCK_MODEL_ID,
    _GENERATED_PATHSPECS,
    _PREIMAGE_CACHE,
    _REMOVED_LINES_CACHE,
    patch_id_pathspec,
)  # noqa: F401
from .branches import (
    branch_date_key,
    branch_support_status,
    get_changed_files,
    get_supported_branches,
    load_versions_manifest,
    parse_eos_date,
    remote_branch_names,
    sort_branches,
)  # noqa: F401
from .textutil import (
    _C_FAMILY_EXT,
    is_boilerplate_line,
    is_c_file,
    is_noise_line,
    norm_ws,
)  # noqa: F401
from .preimage import (
    fix_removed_lines,
    is_test_or_generated_file,
    vulnerable_preimage_present,
    vulnerable_preimage_present_uncached,
)  # noqa: F401
from .gitread import (
    get_commit_diff,
    get_file_on_branch,
    historical_paths,
    show_file,
)  # noqa: F401
from .introducers import find_introducing_commit, find_line_origin  # noqa: F401
from .impact import (
    any_changed_file_present_exact,
    branch_cites_cherry_pick,
    deterministic_impact,
    fold_advisory,
    get_branch_patch_ids,
    introducer_reaches,
    is_already_patched,
    is_branch_affected,
    patch_id_of,
    present_introducers,
    run_ai_advisory,
    source_files_present,
)  # noqa: F401


def __getattr__(name):
    """Forward ``engine.REPO_PATH`` to the live value in :mod:`engine.repo`.

    ``set_repo_path()`` mutates that module global at runtime, so re-exporting it
    with a plain ``from .repo import REPO_PATH`` would bind a stale copy.
    """
    if name == "REPO_PATH":
        return repo.REPO_PATH
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
