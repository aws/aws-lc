"""
Impact verdict and already-patched / patch-id detection.

Layer: impact core (``engine`` package). Builds on ``config`` + ``preimage`` + ``gitread``.
"""

import os
import subprocess
import sys

from .config import patch_id_pathspec
from .gitread import get_file_on_branch
from .preimage import is_test_or_generated_file, vulnerable_preimage_present

# ---------------------------------------------------------------------------
# 8. Impact verdict
# ---------------------------------------------------------------------------


def introducer_reaches(introducing_commits, ref):
    """True if any introducer reaches *ref* by SHA ancestry (Path 1) or patch-id
    equivalence (Path 2 -- a cherry-pick that got a new SHA)."""
    for sha in introducing_commits:
        r = subprocess.run(
            ["git", "merge-base", "--is-ancestor", sha, ref],
            capture_output=True,
            text=True,
        )
        if r.returncode == 0:
            return True
        if r.returncode != 1:
            raise RuntimeError(
                f"git merge-base failed (code {r.returncode}) checking {sha} "
                f"against {ref}: {r.stderr}"
            )
    branch_pids = get_branch_patch_ids(ref)
    for sha in introducing_commits:
        pid = patch_id_of(sha)
        if pid and pid in branch_pids:
            return True
    return False


def source_files_present(changed_files, ref, commit):
    """True if any non-test/-generated changed file exists on *ref* (rename-aware)."""
    source = [
        f for f in changed_files if not is_test_or_generated_file(f)
    ] or changed_files
    return any(get_file_on_branch(f, ref, commit=commit)[0] is not None for f in source)


def deterministic_impact(introducing_commits, ref, commit, changed_files):
    """Deterministic verdict before the AI layer: 'affected', 'not_affected', or
    'inconclusive'. Implements Paths 1/2 (ancestry, patch-id), 2b (positive
    pre-image), 3 (file absence), and 4 (pre-image downgrade)."""
    has_context = bool(commit and changed_files)
    affected = introducer_reaches(introducing_commits, ref)
    # Path 2b: a branch-specific introducer that Paths 1/2 miss, caught by the
    # exact removed lines still being present.
    if not affected and has_context:
        affected = vulnerable_preimage_present(commit, changed_files, ref) is True

    if affected:
        # Path 4: ancestry matched only old shared code -- if the removed lines are
        # provably absent, downgrade to inconclusive (the AI tie-breaker re-flags a
        # reshaped-but-vulnerable branch). Gated by BACKPORT_PREIMAGE_DOWNGRADE.
        if (
            has_context
            and os.environ.get("BACKPORT_PREIMAGE_DOWNGRADE", "1") == "1"
            and vulnerable_preimage_present(commit, changed_files, ref) is False
        ):
            return "inconclusive"
        return "affected"

    # Path 3: none of the fixed source files exist here -> confident not-affected.
    if changed_files and not source_files_present(changed_files, ref, commit):
        return "not_affected"
    return "inconclusive"


def run_ai_advisory(commit, branch, changed_files, introducing_commits, det_affected):
    """Call the advisory AI in the role implied by the deterministic verdict, tag
    the result, and log it. Returns the advisory dict or None."""
    from ai import ai_impact_analysis  # local import avoids an ai<->engine cycle

    det_verdict = "affected" if det_affected else "inconclusive"
    advisory = ai_impact_analysis(
        commit, branch, changed_files, introducing_commits, det_verdict=det_verdict
    )
    if advisory is not None:
        advisory["role"] = "auditor" if det_affected else "tiebreaker"
        advisory["overrode_deterministic"] = False
        # Live progress line; off by default so it doesn't interleave with the
        # replay's per-fix tables (the AI verdict is already in each fix's Notes).
        # Set BACKPORT_VERBOSE=1 to see it.
        if os.environ.get("BACKPORT_VERBOSE"):
            print(
                f"[ai] {advisory['role']} for {branch}: det={det_verdict}, "
                f"likely_affected={advisory['likely_affected']}, "
                f"confidence={advisory['confidence']}",
                file=sys.stderr,
            )
    return advisory


def fold_advisory(det_affected, advisory, commit, changed_files, ref):
    """Combine the deterministic verdict with the advisory, gated by direction so
    the AI never acts alone:
      tie-breaker (inconclusive -> affected): safe, only ADDS a backport;
      auditor (affected -> not affected): can MISS a backport, so suppress only on
      HIGH-confidence "not affected", BACKPORT_AI_SUPPRESS on (default), AND the
      removed lines provably absent.
    """
    if advisory is None:
        return det_affected
    likely = advisory.get("likely_affected")
    conf = advisory.get("confidence")

    if det_affected:
        suppress = os.environ.get("BACKPORT_AI_SUPPRESS", "1") == "1"
        if (
            suppress
            and likely is False
            and conf == "high"
            and vulnerable_preimage_present(commit, changed_files, ref) is False
        ):
            advisory["overrode_deterministic"] = True
            return False
        return True

    # Inconclusive: a "likely affected" upgrades only if a fixed file is actually
    # here at its exact path (else a backport would be an impossible cherry-pick).
    if likely is True:
        if any_changed_file_present_exact(changed_files, ref):
            advisory["overrode_deterministic"] = True
            return True
        advisory["tiebreaker_blocked_no_file"] = True
    return False


def is_branch_affected(
    introducing_commits, branch, commit=None, changed_files=None
) -> "tuple[bool, dict | None]":
    """Is *branch* affected by the fix? Returns (affected, ai_advisory).

    The deterministic engine (see deterministic_impact) owns the verdict; the AI
    layer only nudges it under strict gating (see fold_advisory). Called with
    just (introducers, branch) it is a pure ancestry + patch-id check; called with
    commit + changed_files it also runs the pre-image paths and the AI layer.
    See the README's "How it decides" section for the rationale behind each path.
    """
    ref = f"origin/{branch}"
    verdict = deterministic_impact(introducing_commits, ref, commit, changed_files)
    if verdict == "not_affected":
        return False, None
    det_affected = verdict == "affected"

    # No fix context (the 2-arg call from bucketing): return the deterministic verdict.
    if not (commit and changed_files):
        return det_affected, None

    # Inconclusive AND the code isn't on this branch at all -> confident
    # not-affected; an AI call here could only guess.
    if not det_affected and not any_changed_file_present_exact(changed_files, ref):
        return False, None

    advisory = run_ai_advisory(
        commit, branch, changed_files, introducing_commits, det_affected
    )
    return fold_advisory(det_affected, advisory, commit, changed_files, ref), advisory


def present_introducers(introducing_commits, branch):
    """Subset of *introducing_commits* present on *branch*, by SHA ancestry OR
    patch-id. Finer-grained than is_branch_affected (which stops at the first
    match): lets a caller tell a FULL lineage (all introducers present ->
    confidently affected) from a PARTIAL one (only old shared code present, the
    newer bug-introducing commit absent -> likely over-flag worth review)."""
    ref = f"origin/{branch}"
    present = set()
    for sha in introducing_commits:
        result = subprocess.run(
            ["git", "merge-base", "--is-ancestor", sha, ref], capture_output=True
        )
        if result.returncode == 0:
            present.add(sha)
    remaining = set(introducing_commits) - present
    if remaining:
        branch_pids = get_branch_patch_ids(ref)
        for sha in remaining:
            pid = patch_id_of(sha)
            if pid and pid in branch_pids:
                present.add(sha)
    return present


def any_changed_file_present_exact(changed_files, ref):
    """True if any changed source file exists on *ref* at its EXACT path. Used to
    stop the tie-breaker upgrading a branch where the fix's code isn't present
    (rename-aware matching could falsely link unrelated same-named files)."""
    source = [f for f in (changed_files or ()) if not is_test_or_generated_file(f)]
    for f in source or (changed_files or ()):
        r = subprocess.run(["git", "cat-file", "-e", f"{ref}:{f}"], capture_output=True)
        if r.returncode == 0:
            return True
    return False


# ---------------------------------------------------------------------------
# 9. Already-patched / patch-id
# ---------------------------------------------------------------------------


def branch_cites_cherry_pick(commit, ref):
    """True if a divergent commit on *ref* records `cherry picked from commit
    <full-sha>` for *commit*. Catches bundled/reshaped -x backports whose patch-id
    differs; the exact-SHA match means it never false-negatives. Mainline ref via
    BACKPORT_MAINLINE_REF (default origin/main)."""
    full = subprocess.run(
        ["git", "rev-parse", "--verify", "--quiet", f"{commit}^{{commit}}"],
        capture_output=True,
        text=True,
    )
    if full.returncode != 0 or not full.stdout.strip():
        return False
    full_sha = full.stdout.strip()
    mainline = os.environ.get("BACKPORT_MAINLINE_REF", "origin/main")
    log = subprocess.run(
        ["git", "log", "--format=%B%x00", f"{mainline}..{ref}"],
        capture_output=True,
        text=True,
        errors="replace",
    )
    if log.returncode != 0:
        return False
    return f"cherry picked from commit {full_sha}" in log.stdout


def get_branch_patch_ids(ref):
    """Patch-ids of the branch's DIVERGENT commits (on *ref* but not mainline),
    where cherry-picked backports live. Output read as bytes to tolerate binary
    diffs. Mainline ref via BACKPORT_MAINLINE_REF (default origin/main)."""
    mainline = os.environ.get("BACKPORT_MAINLINE_REF", "origin/main")
    rev_range = f"{mainline}..{ref}"
    log = subprocess.run(
        [
            "git",
            "log",
            "-p",
            "--no-merges",
            "--format=%H",
            rev_range,
            *patch_id_pathspec(),
        ],
        capture_output=True,  # bytes, not text: diffs may contain binary content
    )
    if log.returncode != 0:
        return set()
    pid_proc = subprocess.run(
        ["git", "patch-id", "--stable"],
        input=log.stdout,
        capture_output=True,
    )
    if pid_proc.returncode != 0:
        return set()
    out = pid_proc.stdout.decode("ascii", errors="replace")
    return {line.split()[0] for line in out.splitlines() if line.split()}


def is_already_patched(commit, branch):
    """Whether *commit*'s change is already on *branch* -- as a direct ancestor
    (forked after the fix), a `-x` cherry-pick annotation, or a matching patch-id
    (manual cherry-pick under a new SHA). Patch-ids exclude generated files."""
    ref = f"origin/{branch}"

    # Fast path: the exact commit is an ancestor (branch forked after the fix).
    # The divergent-only patch-id scan below would otherwise miss this.
    anc = subprocess.run(
        ["git", "merge-base", "--is-ancestor", commit, ref], capture_output=True
    )
    if anc.returncode == 0:
        return True

    # A `-x` annotation proves a cherry-pick even when a reshaped/bundled backport
    # has a different patch-id.
    if branch_cites_cherry_pick(commit, ref):
        return True

    target_pid = patch_id_of(commit)
    if not target_pid:
        return False

    branch_pids = get_branch_patch_ids(ref)
    return target_pid in branch_pids


def patch_id_of(commit):
    """Return the patch-id (content hash) of a single commit, or None on failure."""
    show = subprocess.run(
        ["git", "show", commit, *patch_id_pathspec()],
        capture_output=True,  # bytes: the commit may touch binary files
    )
    if show.returncode != 0:
        return None
    pid = subprocess.run(
        ["git", "patch-id", "--stable"],
        input=show.stdout,
        capture_output=True,
    )
    if pid.returncode != 0 or not pid.stdout.strip():
        return None
    return pid.stdout.decode("ascii", errors="replace").split()[0]
