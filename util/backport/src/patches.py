"""
Patch handling.

Layer: input plumbing. Builds on ``gitutil`` + ``runstate``; used by the
``analyze`` / ``apply`` / ``resolve`` commands to obtain the fix to analyze.

Two jobs: (1) turn a patch -- a ``git diff`` or ``git format-patch`` -- into a
real (temporary) commit the engine can analyze, and (2) resolve where a run's
patch comes from (``--commit``, an explicit ``--patch`` file, the working tree,
or a saved run). Plus the pre-analysis test-file confirmation.
"""

import re
from contextlib import contextmanager
from pathlib import Path
from typing import Iterator, Optional, Set, Tuple

from common import BackportError
from gitutil import git, ref_exists, temp_worktree
from runstate import load_run


# --------------------------------------------------------------------------
# Turning a patch into a real (temporary) commit
# --------------------------------------------------------------------------


def is_format_patch(patch: str) -> bool:
    """True if this is ``git format-patch`` output rather than a plain ``git diff``.

    ``git format-patch`` writes the patch as an email (it begins with a
    ``From <sha> <date>`` line and has Subject:/author headers); it is applied
    with ``git am``. A plain ``git diff`` has no such header and is applied with
    ``git apply``. We check the first line to decide which to use.
    """
    head = patch.lstrip().splitlines()[:1]
    return bool(head) and head[0].startswith("From ")


def commit_message_from_patch(
    patch: str, fallback: str = "Backport candidate (from patch)"
) -> str:
    """Use the patch's ``Subject:`` line as the commit message, else a fallback."""
    for line in patch.splitlines():
        if line.startswith("Subject:"):
            subject = line[len("Subject:") :].strip()
            # Strip a leading git-format-patch "[PATCH ...]" tag (a literal prefix,
            # not a character set -- str.lstrip would chew into "[PATCH v2] foo").
            subject = re.sub(r"^\[PATCH[^\]]*\]\s*", "", subject).strip()
            return subject or fallback
    return fallback


@contextmanager
def commit_from_patch(
    patch: str, base: str, three_way: bool = False
) -> "Iterator[str]":
    """Make the patch into a real, temporary commit and yield its SHA.

    The engine works on commits, but the caller gives us a patch (of a committed
    change or of uncommitted edits, it does not matter). So we check out *base* in
    a throwaway ``git worktree``, pipe the patch into ``git apply``/``git am``
    there, commit it, and hand back the new commit's SHA. On exit the worktree is
    deleted; the commit object lingers in git's shared object store for the rest
    of the process, which is all the engine needs to read it.
    """
    if not ref_exists(base):
        raise BackportError(
            f"base ref '{base}' not found. Fetch the mainline first "
            f"(git fetch origin) or pass --base <ref>."
        )

    # The patch is piped to git over stdin, so it never gets written to disk.
    with temp_worktree(base) as worktree:
        applied = False
        if is_format_patch(patch):
            am_args = ["am", "--3way"] if three_way else ["am"]
            am = git(*am_args, check=False, cwd=worktree, stdin=patch)
            if am.returncode == 0:
                applied = True
            else:
                git("am", "--abort", check=False, cwd=worktree)

        if not applied:
            apply_args = ["apply", "--3way"] if three_way else ["apply"]
            ap = git(*apply_args, check=False, cwd=worktree, stdin=patch)
            if ap.returncode != 0:
                raise BackportError(
                    "patch did not apply onto "
                    f"{base}:\n{(ap.stderr or ap.stdout).strip()}\n"
                    "If your local mainline has drifted, retry with --3way."
                )

        # Collapse whatever we just applied -- a single diff, or one *or more*
        # format-patch commits from `git am` -- into ONE synthetic commit whose
        # parent is *base*. `git reset --soft` rewinds HEAD to base while keeping
        # the applied tree staged, so the resulting commit's diff is the fix's
        # *net* change. This is what makes a fix spread across several small
        # commits analyze identically to one squashed commit.
        git("reset", "--soft", base, cwd=worktree)
        git("add", "-A", cwd=worktree)
        git(
            "-c",
            "user.name=backport-cli",
            "-c",
            "user.email=backport-cli@local",
            "commit",
            "--quiet",
            "--allow-empty",
            "-m",
            commit_message_from_patch(patch),
            cwd=worktree,
        )
        sha = git("rev-parse", "HEAD", cwd=worktree).stdout.strip()
        yield sha


# --------------------------------------------------------------------------
# Where does this run's patch come from?
# --------------------------------------------------------------------------


def is_empty_patch(patch: str) -> bool:
    """True if the patch has no diff content (blank file or only blank lines)."""
    return not patch.strip()


def range_endpoints(spec: str) -> "Optional[Tuple[str, str]]":
    """If *spec* is a commit range, return ``(base, head)`` to diff, else None.

    ``A..B`` -> ``(A, B)`` (the net change from A to B).
    ``A...B`` -> ``(merge-base(A, B), B)`` (the change on B since it forked from A;
    handy for "everything on my feature branch", e.g. ``origin/main...HEAD``).
    An empty side defaults to HEAD.
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


def explicit_patch_source(args) -> "Optional[Tuple[str, str, str]]":
    """``(patch, base, source)`` for an explicit ``--commit`` or ``--patch``, else None.

    The one place that turns ``--commit`` or ``--patch`` into a patch. ``--commit``
    accepts either a single ref (reconstructed via ``format-patch -1``, base
    ``<ref>^``) or a **range** ``A..B`` / ``A...B`` -- the latter diffs the whole
    span into one aggregate patch, so a fix made of several small commits is
    analyzed as its net change (base = the range's start). ``--patch`` reads the
    file (base origin/main). Shared by :func:`read_patch` (analyze) and
    :func:`resolve_patch_and_base` (apply). *source* is ``"commit"`` or ``"patch"``.
    """
    if getattr(args, "commit", None):
        rng = range_endpoints(args.commit)
        if rng:
            base, head = rng
            return git("diff", f"{base}..{head}").stdout, (args.base or base), "commit"
        patch = git("format-patch", "-1", "--stdout", args.commit).stdout
        return patch, (args.base or f"{args.commit}^"), "commit"
    if getattr(args, "patch", None):
        return Path(args.patch).read_text(), (args.base or "origin/main"), "patch"
    return None


def read_patch(args) -> "Tuple[str, str, bool]":
    """Return ``(patch, base, from_file)`` for ``analyze``.

    Sources, in priority order:
      --commit <ref>  reconstruct the fix from an existing commit internally
                      (base defaults to ``<ref>^``); handy for testing a past fix.
      <patch file>    read the given git diff / format-patch (base origin/main).
      (nothing)       capture the repo's uncommitted diff ``git diff HEAD``
                      (base = current HEAD) -- the normal pre-merge flow.
    """
    explicit = explicit_patch_source(args)
    if explicit:
        patch, base, source = explicit
        return patch, base, source == "patch"
    diff = git("diff", "HEAD").stdout
    base = args.base or git("rev-parse", "HEAD").stdout.strip()
    return diff, base, False


def resolve_patch_and_base(args) -> "Tuple[str, str, Optional[dict]]":
    """Return ``(patch, base, run)`` for ``apply``.

    With an explicit ``--commit``/``--patch``, read those and skip the saved run.
    Otherwise reuse the patch and base cached by the last ``analyze``.
    """
    explicit = explicit_patch_source(args)
    if explicit:
        patch, base, _ = explicit
        return patch, base, None
    run = load_run()
    base = args.base or run.get("base", "origin/main")
    return run["patch"], base, run


# --------------------------------------------------------------------------
# Test-file confirmation (analyze)
# --------------------------------------------------------------------------

_TEST_SUFFIXES = ("_test.cc", "_test.cpp", "_test.c", "_test.cxx")


def patch_paths(patch: str) -> Set[str]:
    """File paths touched by the patch, parsed from the diff headers."""
    paths: Set[str] = set()
    for line in patch.splitlines():
        if line.startswith("diff --git ") and " b/" in line:
            paths.add(line.split(" b/", 1)[1].strip())
        elif line.startswith("+++ b/"):
            p = line[len("+++ b/") :].strip()
            if p and p != "/dev/null":
                paths.add(p)
    return paths


def ask_yn(prompt: str) -> bool:
    """Prompt until the user answers Y or N. Returns True for Y."""
    while True:
        try:
            ans = input(f"{prompt} [Y/N] ").strip().lower()
        except EOFError:
            # no input available (e.g. stdin closed) -> treat as a safe abort
            return False
        if ans in ("y", "yes"):
            return True
        if ans in ("n", "no"):
            return False
        print("Please answer Y or N.")


def confirm_test_file(patch: str) -> bool:
    """Confirm the patch's test file before analysis. Returns True to proceed.

    AWS-LC tests usually live next to the fix as a ``*_test.cc`` file in the same
    diff. If one is present, confirm it is the right test; if none is present,
    confirm the user wants to proceed without one. Answering N aborts.
    """
    tests = sorted(p for p in patch_paths(patch) if p.endswith(_TEST_SUFFIXES))
    if tests:
        print(f"Test file found in the patch: {', '.join(tests)}")
        return ask_yn("Is this the test file for your patch?")
    print("No test file (e.g. *_test.cc) found in the patch.")
    return ask_yn("Proceed without a test file?")
