"""
Everything that shells out to git.

Which checkout we're pointed at, the command runners, throwaway worktrees, the
cherry-pick used by `apply` and `publish`, working out which commit(s) a fix is,
and the file/diff reads that follow renames.

Only imports util.config, so it can't cause import cycles.
"""

import os
import shutil
import subprocess
import tempfile
from contextlib import contextmanager
from typing import Dict, Iterator, List, Optional, Sequence, Tuple

from util.config import (
    MAINLINE_REF,
    MAX_DIFF_BYTES,
    MAX_FILE_BYTES,
    BackportError,
    is_test_or_generated_file,
)


# --- Repository targeting -------------------------------------------------

# The checkout every git command runs in. None means "use the current directory"
# (the replay bench relies on that -- it chdirs into a sandbox).
REPO_PATH = None


def set_repo_path(path):
    """Point the tool at a checkout; None goes back to using the current directory."""
    global REPO_PATH
    REPO_PATH = os.path.abspath(path) if path else None


def repo_path():
    """The active checkout, or None.

    Call this instead of importing REPO_PATH -- set_repo_path() reassigns it, so an
    imported copy would still be None.
    """
    return REPO_PATH


def run_in_repo(cmd, **kwargs):
    """Run a command in REPO_PATH. Returns the result; never raises.

    Compare run()/git() below, which raise BackportError when a command fails.
    """
    if REPO_PATH is not None and kwargs.get("cwd") is None:
        kwargs["cwd"] = REPO_PATH
    return subprocess.run(list(cmd), **kwargs)


def git_in_repo(args, **kwargs):
    """Run a git command in REPO_PATH. Never raises; see run_in_repo()."""
    return run_in_repo(["git", *args], **kwargs)


# --- Low-level command runners --------------------------------------------


def run(
    args: Sequence[str],
    check: bool = True,
    cwd: Optional[str] = None,
    stdin: Optional[str] = None,
):
    """Run a command and capture its output. Raises BackportError if it fails.

    Runs in REPO_PATH unless *cwd* says otherwise (worktrees pass their own).
    """
    if cwd is None:
        cwd = REPO_PATH
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
    """Run a git command. Raises BackportError if it fails; see run()."""
    return run(["git", *args], check=check, cwd=cwd, stdin=stdin)


def ref_exists(ref: str) -> bool:
    """True if *ref* resolves to an object in the repo."""
    return git("rev-parse", "--verify", "--quiet", ref, check=False).returncode == 0


@contextmanager
def temp_worktree(base: str, prefix: str = "backport-") -> "Iterator[str]":
    """Check *base* out in a throwaway worktree and yield its path.

    Lets us cherry-pick without touching the user's files. The worktree is deleted
    afterwards, but any commits made in it stay in the repo's object store, which
    is all we need.
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


# --- Cherry-pick primitive (shared by `apply` and `publish`) --------------


# Author for commits the tool makes itself, so they're never attributed to the
# user. Passed with `git -c`, so the repo's config is left alone.
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
    """Files still conflicted in *wt*, as ``{"path", "kind"}``.

    *kind* is git's own wording ("both modified", "deleted by us", ...). Re-call it
    after each `git add` to see what's left -- that's how `resolve` tracks progress.
    """
    out = git("status", "--porcelain", cwd=wt).stdout
    files: List[dict] = []
    for line in out.splitlines():
        xy, path = line[:2], line[3:].strip()
        if "U" in xy or xy in ("AA", "DD"):
            files.append({"path": path, "kind": _CONFLICT_KIND.get(xy, "conflict")})
    return files


def file_has_conflict_markers(path: str) -> bool:
    """True if *path* still has conflict markers in it.

    Checked before staging a file the user says is resolved, so a half-edited file
    never gets committed.
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
    """Turn on git rerere, so resolving a conflict once reuses it next time.

    Handy for the FIPS twin branches, which usually conflict identically. rerere's
    autoupdate is left OFF on purpose: the reused resolution stays unstaged so
    `resolve` can still show it to the user instead of committing it silently.
    """
    git("config", "rerere.enabled", "true", check=False)


def resolve_commit(commit_ish: str) -> "Tuple[str, str]":
    """Resolve *commit_ish* to ``(sha, subject)``.

    A merge commit's own diff is empty -- the change is on the side that got merged
    in -- so we switch to its second parent and say so. Raises BackportError if the
    commit isn't here.
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

    Never pushes or opens a PR. Returns ``(status, detail, extra)``:
      clean    -> branch `backport/<branch>/<run_id>` created. *extra* lists any
                  test/generated files whose conflicting hunks we dropped.
      conflict -> a real source conflict; aborted, nothing left behind. *extra* is
                  the conflicting files. Use `resolve` to fix it by hand.
      error    -> missing branch, or git failed.
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
                # Only tests/generated files clashed, so the actual fix applied.
                # Keep the branch's versions of those and finish the pick -- a test
                # clash shouldn't force manual resolution.
                if (
                    conflicts
                    and all(is_test_or_generated_file(c["path"]) for c in conflicts)
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
    """Finish a cherry-pick that only clashed on tests/generated files, by keeping
    the branch's version of each. False if it couldn't finish, so the caller aborts
    and treats it as a real conflict."""
    for c in conflicts:
        path = c["path"]
        # Take the target branch's version; if the branch deleted the file, drop it.
        if git("checkout", "HEAD", "--", path, check=False, cwd=wt).returncode != 0:
            git("rm", "--force", "--quiet", "--", path, check=False, cwd=wt)
        else:
            git("add", "--", path, cwd=wt)
    # Nothing of the fix left staged means there's nothing to backport.
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


# --- Which commit(s) are we analyzing? ------------------------------------


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
    """Which commit(s) to analyze, as ``(sha, base)``.

      --commit <ref>       that commit; base is its parent
      --commit A..B/A...B  the span from A to B
      (nothing)            your branch's commits since it left the mainline

    The commits already exist, so nothing is extracted or checked out. A span of
    several commits is squashed into one commit object with `git commit-tree`, so a
    fix split across commits is analyzed as its net change.
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


# --- git diff-tree parsers ------------------------------------------------


def changed_files_with_status(commit: str) -> "Tuple[List[str], List[str]]":
    """Files *commit* touches, as ``(all_files, traceable_files)``.

    traceable_files leaves out files the fix ADDED -- a brand-new file has no
    history, so there's no earlier commit to blame for it.

    Parses `git diff-tree --name-status`, one line per file::

        M\tcrypto/aead.c          modified
        A\ttls/new_feature.c      added
        R100\told.c\tnew.c        renamed (new path is last)
    """
    output = git_in_repo(
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
        status, path = columns[0], columns[-1]  # last column is the (new) path
        changed_files.append(path)
        if not status.startswith("A"):  # "A" = added by this fix
            traceable_files.append(path)
    return changed_files, traceable_files


def branch_paths_by_basename(ref: str) -> "Dict[str, List[str]]":
    """Every path on *ref*, grouped by filename.

    Used to look for a file the fix touched that moved somewhere git couldn't
    trace. Returns full paths, not just names, so the caller can check the contents
    -- a filename match alone means little when `internal.h` appears 41 times.
    """
    out = git_in_repo(
        ["ls-tree", "-r", "--name-only", ref],
        check=False,
        capture_output=True,
        text=True,
    ).stdout
    grouped: "Dict[str, List[str]]" = {}
    for path in out.splitlines():
        path = path.strip()
        if path:
            grouped.setdefault(os.path.basename(path), []).append(path)
    return grouped


# --- Which checkout are we operating on? ----------------------------------


def target_repo(args) -> str:
    """Work out which checkout to use, point REPO_PATH at it, and chdir there.

    Order: --repo, then $BACKPORT_REPO_PATH, then the current directory -- so the
    tool works on "the repo I'm standing in" unless told otherwise. Returns the
    top-level path; raises BackportError if it isn't a git repo.
    """
    """Work out which checkout to use and point REPO_PATH at it.

    Order: --repo, then $BACKPORT_REPO_PATH, then the current directory -- so running
    `./util/backport/backport` from the top of a checkout just works. Returns the
    top-level path; raises BackportError if it isn't a git repo.

    Deliberately does NOT chdir. Every git call goes through run_in_repo/git_in_repo
    or passes an explicit cwd, so the tool never depends on -- or changes -- the
    process working directory.
    """
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
            f"'{repo}' is not inside a git repository.\n"
            "  Run this from the top of an AWS-LC checkout, or pass --repo <path>."
        )
    repo_top = top.stdout.strip()
    set_repo_path(repo_top)
    return repo_top


# --- Rename-aware file and diff reads -------------------------------------


def get_commit_diff(commit):
    """Return the full diff for *commit* as a string (capped at MAX_DIFF_BYTES)."""
    result = git_in_repo(
        ["show", "--stat", "-p", commit],
        capture_output=True,
        text=True,
        errors="replace",
    )
    if result.returncode != 0:
        return ""
    return result.stdout[:MAX_DIFF_BYTES]


def show_file(ref, path):
    """Raw contents of *path* at *ref*, or None if it doesn't exist there."""
    result = git_in_repo(
        ["show", f"{ref}:{path}"],
        capture_output=True,
        text=True,
        errors="replace",
    )
    if result.returncode != 0:
        return None
    return result.stdout


def historical_paths(commit, file_path, limit=6):
    """Paths *file_path* has occupied over its history (current first, then older
    names, following renames) as of *commit* -- so we can find the file on a
    branch that forked before a rename."""
    paths = [file_path]
    result = git_in_repo(
        [
            "log",
            "--follow",
            "--name-status",
            "--format=",
            commit,
            "--",
            file_path,
        ],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        return paths
    seen = {file_path}
    for line in result.stdout.splitlines():
        parts = line.split("\t")
        # Rename entries look like: R100<TAB>old/path<TAB>new/path
        if parts and parts[0].startswith("R") and len(parts) >= 3:
            old = parts[1].strip()
            if old and old not in seen:
                paths.append(old)
                seen.add(old)
                if len(paths) >= limit:
                    break
    return paths


def get_file_on_branch(file_path, branch_ref, commit=None):
    """(content, resolved_path) for *file_path* on *branch_ref*, capped at
    MAX_FILE_BYTES. If absent at the current path and *commit* is given,
    follows rename history to try earlier paths. (None, None) if not found."""
    content = show_file(branch_ref, file_path)
    if content is not None:
        return content[:MAX_FILE_BYTES], file_path
    if commit:
        for older in historical_paths(commit, file_path):
            if older == file_path:
                continue
            content = show_file(branch_ref, older)
            if content is not None:
                return content[:MAX_FILE_BYTES], older
    return None, None
