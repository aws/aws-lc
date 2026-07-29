"""
Ancestry / patch-id reachability and already-patched detection.

Layer: impact core (``engine`` package). Builds on ``config``.

The per-branch VERDICT lives in ``verdicts.classify_branch`` (one implementation,
shared by the CLI and the replay bench); this module supplies the primitives it
asks about.
"""

import os
import subprocess

from .config import patch_id_pathspec

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


def present_introducers(introducing_commits, branch):
    """Subset of *introducing_commits* present on *branch*, by SHA ancestry OR
    patch-id. Finer-grained than :func:`introducer_reaches` (which stops at the
    first match): lets a caller tell a FULL lineage (all introducers present ->
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
