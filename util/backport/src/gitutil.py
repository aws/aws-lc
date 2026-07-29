"""
Git plumbing and repository targeting.

Layer: git plumbing. Builds on ``engine`` (for REPO_PATH) + ``common``; used by
``verdicts`` and the command modules.

Everything that shells out to git lives here: the low-level ``run``/``git``
wrappers, throwaway worktrees, the cherry-pick primitive shared by ``apply`` and
``ci``, resolving which commit(s) a fix is, the two ``git diff-tree`` parsers, and
the logic that points the engine at the right AWS-LC checkout.
"""

import os
import shutil
import subprocess
import tempfile
from contextlib import contextmanager
from typing import Iterator, List, Optional, Sequence, Set, Tuple

import engine as bot
from common import BackportError


# --------------------------------------------------------------------------
# Low-level command runners
# --------------------------------------------------------------------------


def run(
    args: Sequence[str],
    check: bool = True,
    cwd: Optional[str] = None,
    stdin: Optional[str] = None,
):
    """Run a command and capture its output.

    Defaults to the engine's configured repo path; an explicit *cwd* (used by the
    throwaway worktrees) always wins. *stdin* is fed to the command's standard
    input -- used to pipe a patch into ``git apply``/``git am``.
    """
    if cwd is None:
        cwd = bot.REPO_PATH
    p = subprocess.run(list(args), capture_output=True, text=True, cwd=cwd, input=stdin)
    if check and p.returncode != 0:
        raise BackportError(
            f"command failed: {' '.join(args)}\nstdout: {p.stdout}\nstderr: {p.stderr}"
        )
    return p


def git(
    *args: str,
    check: bool = True,
    cwd: Optional[str] = None,
    stdin: Optional[str] = None,
):
    """Run a git subcommand (thin wrapper over :func:`run`)."""
    return run(["git", *args], check=check, cwd=cwd, stdin=stdin)


def ref_exists(ref: str) -> bool:
    """True if *ref* resolves to an object in the repo."""
    return git("rev-parse", "--verify", "--quiet", ref, check=False).returncode == 0


@contextmanager
def temp_worktree(base: str, prefix: str = "backport-") -> "Iterator[str]":
    """Check out *base* in a throwaway detached ``git worktree`` and yield its path.

    This lets us cherry-pick into a clean tree without touching the user's working
    copy. On exit the worktree and its temp parent dir are removed; any commits
    made inside it survive in git's shared object store, which is all the engine
    and the caller need.
    """
    scratch_dir = tempfile.mkdtemp(prefix=prefix)
    worktree = os.path.join(scratch_dir, "wt")
    try:
        git("worktree", "add", "--detach", "--quiet", worktree, base)
        yield worktree
    finally:
        git("worktree", "remove", "--force", worktree, check=False)
        shutil.rmtree(scratch_dir, ignore_errors=True)
        git("worktree", "prune", check=False)


# --------------------------------------------------------------------------
# Cherry-pick primitive (shared by `apply` and `ci`)
# --------------------------------------------------------------------------


# Identity for the commits the tool creates itself (a collapsed multi-commit span,
# or completing a cherry-pick), so they are never attributed to the user. Passed as
# `git -c ...` so nothing in the repo's config is modified.
BOT_IDENTITY = (
    "-c",
    "user.name=backport-cli",
    "-c",
    "user.email=backport-cli@local",
)

# git status porcelain XY codes for unmerged paths -> git's long-format wording.
_CONFLICT_KIND = {
    "DD": "both deleted",
    "AU": "added by us",
    "UD": "deleted by them",
    "UA": "added by them",
    "DU": "deleted by us",
    "AA": "both added",
    "UU": "both modified",
}


def unmerged_files(wt: str) -> List[dict]:
    """List the still-unmerged files in *wt* (a conflicted cherry-pick), each as
    ``{"path", "kind"}`` where *kind* is git's own conflict wording (``both
    modified`` / ``both added`` / ``deleted by us`` / ...), and *path* is the
    repo-relative path.

    Uses ``git status --porcelain`` (the U/AA/DD codes). Call before staging, and
    re-call after each ``git add`` to see what remains -- this is how ``resolve``
    tracks progress.
    """
    out = git("status", "--porcelain", cwd=wt).stdout
    files: List[dict] = []
    for line in out.splitlines():
        xy, path = line[:2], line[3:].strip()
        if "U" in xy or xy in ("AA", "DD"):
            files.append({"path": path, "kind": _CONFLICT_KIND.get(xy, "conflict")})
    return files


def file_has_conflict_markers(path: str) -> bool:
    """True if *path* still contains git conflict markers.

    ``resolve`` calls this before staging a file the user *claims* is resolved, so
    a half-edited file with leftover markers is never committed.
    """
    try:
        with open(path, errors="replace") as fh:
            for line in fh:
                if line.startswith("<<<<<<<") or line.startswith(">>>>>>>"):
                    return True
    except OSError:
        return False
    return False


def enable_rerere() -> None:
    """Turn on git rerere ("reuse recorded resolution") for this repo.

    With rerere on, resolving a conflict once records the resolution; an identical
    conflict later (e.g. on a FIPS twin branch) is auto-applied to the working
    tree. autoupdate is deliberately left OFF: the auto-applied file stays
    *unmerged* (marker-free) so ``resolve`` can still surface it for the user to
    verify before it is staged, rather than silently committing it.
    """
    git("config", "rerere.enabled", "true", check=False)


def resolve_commit(commit_ish: str) -> "Tuple[str, str]":
    """Resolve *commit_ish* to ``(fix_sha, subject)``.

    A merge commit's own diff-tree is empty (the real change is on the merged-in
    side), so when handed one we transparently re-point to its second parent (the
    PR head) and print a note. Squash/normal single-parent commits pass through
    unchanged. Raises :class:`BackportError` if the commit is not in the checkout.
    """
    fix = git("rev-parse", "--verify", f"{commit_ish}^{{commit}}", check=False)
    if fix.returncode != 0:
        raise BackportError(f"commit '{commit_ish}' not found in the checkout.")
    fix_sha = fix.stdout.strip()
    parents = git("rev-list", "--parents", "-n", "1", fix_sha).stdout.split()
    if len(parents) > 2:  # sha + 2+ parent shas => merge commit
        merged_head = git("rev-parse", f"{fix_sha}^2").stdout.strip()
        print(
            f"note: {fix_sha[:10]} is a merge commit; analyzing the merged-in "
            f"commit {merged_head[:10]} instead."
        )
        fix_sha = merged_head
    subject = git("log", "-1", "--format=%s", fix_sha).stdout.strip()
    return fix_sha, subject


def cherry_pick_local(
    fix_sha: str, branch: str, run_id: str
) -> "Tuple[str, Optional[str], List[dict]]":
    """Cherry-pick *fix_sha* onto ``origin/<branch>`` in a throwaway worktree.

    Returns ``(status, detail, extra)``:
      - ``("clean", local_branch, dropped)`` -- applied; the local branch
        ``backport/<branch>/<run_id>`` is created. *dropped* is normally ``[]``;
        if the pick conflicted **only** in test/generated files, those hunks are
        dropped (the branch keeps its own tests, the source fix applies) and the
        pick is completed -- *dropped* then lists those files so the caller can
        note them.
      - ``("conflict", None, [{path, kind}, ...])`` -- a real (source) conflict;
        the attempt is ABORTED. Nothing is committed and no branch is left behind.
        Use the interactive ``resolve`` command to fix it live in a worktree.
      - ``("error", message, [])`` -- the branch/ref was missing or git failed.

    Never pushes or opens a PR.
    """
    ref = f"origin/{branch}"
    if not ref_exists(ref):
        return "error", f"{ref} not found", []
    local_branch = f"backport/{branch}/{run_id}"
    try:
        with temp_worktree(ref, prefix="backport-cp-") as wt:
            pick = git("cherry-pick", fix_sha, check=False, cwd=wt)
            dropped: List[dict] = []
            if pick.returncode != 0:
                conflicts = unmerged_files(wt)
                # Test/generated-only conflict: the source fix applied cleanly and
                # only a test/generated file clashed. Drop those hunks (keep the
                # branch's version) and finish the pick, so a trivial test clash
                # counts as a clean backport instead of manual resolution.
                if (
                    conflicts
                    and all(bot.is_test_or_generated_file(c["path"]) for c in conflicts)
                    and drop_and_continue(wt, conflicts)
                ):
                    dropped = conflicts
                else:
                    git("cherry-pick", "--abort", check=False, cwd=wt)
                    return "conflict", None, conflicts
            new_sha = git("rev-parse", "HEAD", cwd=wt).stdout.strip()
            git("branch", "-f", local_branch, new_sha)
            return "clean", local_branch, dropped
    except BackportError as exc:
        return "error", str(exc), []


def drop_and_continue(wt: str, conflicts: List[dict]) -> bool:
    """Resolve a test/generated-only conflict by restoring the branch's version of
    each conflicting file (dropping the fix's test churn), then completing the
    cherry-pick. Returns True on success, False if it could not finish cleanly
    (leaving the caller to abort and treat it as a real conflict)."""
    for c in conflicts:
        path = c["path"]
        # Restore HEAD's (the target branch's) version; if the branch deleted the
        # file, drop it entirely.
        if git("checkout", "HEAD", "--", path, check=False, cwd=wt).returncode != 0:
            git("rm", "--force", "--quiet", "--", path, check=False, cwd=wt)
        else:
            git("add", "--", path, cwd=wt)
    # If nothing of the source fix remains staged, there is nothing to backport.
    if git("diff", "--cached", "--quiet", check=False, cwd=wt).returncode == 0:
        return False
    cont = git(
        *BOT_IDENTITY,
        "-c",
        "core.editor=true",
        "cherry-pick",
        "--continue",
        check=False,
        cwd=wt,
    )
    return cont.returncode == 0


# --------------------------------------------------------------------------
# Which commit(s) are we analyzing?
# --------------------------------------------------------------------------

MAINLINE_REF = os.environ.get("BACKPORT_MAINLINE_REF", "origin/main")


def range_endpoints(spec: str) -> "Optional[Tuple[str, str]]":
    """If *spec* is a commit range, return ``(base, head)``, else None.

    ``A..B`` -> ``(A, B)``. ``A...B`` -> ``(merge-base(A, B), B)`` -- the change on
    B since it forked from A. An empty side defaults to HEAD.
    """
    for sep in ("...", ".."):
        if sep in spec:
            left, right = spec.split(sep, 1)
            left, right = (left or "HEAD"), (right or "HEAD")
            if sep == "...":
                base = git("merge-base", left, right).stdout.strip()
                if not base:
                    raise BackportError(f"no merge base for range '{spec}'.")
                return base, right
            return left, right
    return None


def _rev(ref: str) -> str:
    """Resolve *ref* to a commit SHA, or raise a user-facing error."""
    r = git("rev-parse", "--verify", f"{ref}^{{commit}}", check=False)
    if r.returncode != 0:
        raise BackportError(f"'{ref}' is not a commit in this checkout.")
    return r.stdout.strip()


def resolve_fix_commit(args) -> "Tuple[str, str]":
    """Resolve which real commit(s) to analyze, as ``(fix_sha, base)``.

    - ``--commit <ref>``          the commit itself; base is its first parent.
    - ``--commit A..B``/``A...B`` the span from A to B.
    - (nothing)                   the current branch since it diverged from the
      mainline, i.e. ``git merge-base <mainline> HEAD``.

    The commits already exist, so nothing is extracted, applied, or checked out.
    A span of more than one commit is collapsed into a single commit object with
    ``git commit-tree`` -- pure plumbing, no worktree -- so the engine sees the
    span's *net* change and a multi-commit fix analyzes like a squashed one.
    """
    spec = getattr(args, "commit", None) or f"{MAINLINE_REF}...HEAD"
    endpoints = range_endpoints(spec)
    if endpoints is None:
        fix_sha = _rev(spec)
        return fix_sha, f"{fix_sha}^"

    base_sha, head_sha = _rev(endpoints[0]), _rev(endpoints[1])
    n = int(git("rev-list", "--count", f"{base_sha}..{head_sha}").stdout.strip() or 0)
    if n == 0:
        raise BackportError(
            f"no commits in '{spec}' -- nothing to analyze.\n"
            "  Commit your fix, or name it explicitly with --commit <ref>."
        )
    if n == 1:
        return head_sha, base_sha

    tree = git("rev-parse", f"{head_sha}^{{tree}}").stdout.strip()
    subject = git("log", "-1", "--format=%s", head_sha).stdout.strip()
    synthetic = git(
        *BOT_IDENTITY,
        "commit-tree",
        tree,
        "-p",
        base_sha,
        "-m",
        f"[net change of {n} commits] {subject}",
    ).stdout.strip()
    return synthetic, base_sha


# --------------------------------------------------------------------------
# git diff-tree parsers
# --------------------------------------------------------------------------


def changed_files_with_status(commit: str) -> "Tuple[List[str], List[str]]":
    """Return ``(changed_files, traceable_files)`` for *commit*.

    ``git diff-tree --name-status`` prints one line per changed file, e.g.::

        M\tcrypto/aead.c          modified
        A\ttls/new_feature.c      added
        R100\told.c\tnew.c        renamed (the new path is the last column)

    - ``changed_files``: every path the fix touches.
    - ``traceable_files``: the same, minus files this fix *added* (status ``A``).
      A brand-new file has no prior history, so there is no introducing commit to
      trace for it; we exclude it so introducer detection does not choke.
    """
    output = bot.git_in_repo(
        ["diff-tree", "--no-commit-id", "--name-status", "-r", commit],
        capture_output=True,
        text=True,
    ).stdout

    changed_files: List[str] = []
    traceable_files: List[str] = []
    for line in output.splitlines():
        if not line.strip():
            continue
        columns = line.split("\t")
        status, path = columns[0], columns[-1]  # last column = the (new) path
        changed_files.append(path)
        if not status.startswith("A"):  # skip files added by this fix
            traceable_files.append(path)
    return changed_files, traceable_files


def branch_basenames(ref: str) -> Set[str]:
    """Set of file basenames present anywhere on *ref*.

    A conservative anti-false-negative guard: a same-named file under a path our
    rename trace missed means the code may still be on the branch.
    """
    out = bot.git_in_repo(
        ["ls-tree", "-r", "--name-only", ref],
        check=False,
        capture_output=True,
        text=True,
    ).stdout
    return {os.path.basename(p) for p in out.splitlines() if p.strip()}


# --------------------------------------------------------------------------
# Repository targeting
# --------------------------------------------------------------------------


def target_repo(args) -> str:
    """Resolve + activate the AWS-LC checkout for this run.

    Confirms it is a git repo, points the engine at its top level, and chdir's
    there. Returns the top-level path; raises :class:`BackportError` if the path
    is not inside a git repository.
    """
    # --repo, then $BACKPORT_REPO_PATH, then the cwd: the tool operates on
    # "the repo I'm standing in" unless told otherwise.
    repo = (
        getattr(args, "repo", None)
        or os.environ.get("BACKPORT_REPO_PATH")
        or os.getcwd()
    )
    top = subprocess.run(
        ["git", "-C", repo, "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
    )
    if top.returncode != 0:
        raise BackportError(
            f"'{repo}' is not inside a git repository "
            "(use --repo <path> or set BACKPORT_REPO_PATH)."
        )
    repo_top = top.stdout.strip()
    bot.set_repo_path(repo_top)
    # The engine's internal git calls use the process working directory, so point
    # it at the repo. Throwaway worktrees always pass an explicit cwd, so they are
    # unaffected.
    os.chdir(repo_top)
    return repo_top
