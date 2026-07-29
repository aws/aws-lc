"""
The deterministic analysis engine.

Layer: impact core. Builds on ``util.config`` + ``util.git``; deliberately does
NOT import the AI layer -- ``engine.analysis`` owns the deterministic verdict, and
the commands decide when to consult ``engine.ai``.

Reading order, roughly the order a run uses them:
  1. text/line normalizers -- what counts as a distinctive line
  2. the vulnerable pre-image -- are the lines the fix removes still on a branch?
  3. supported-branch resolution -- which release branches exist, and their order
  4. introducer tracing -- which commit(s) wrote the lines the fix changes
  5. ancestry / patch-id reachability and already-patched detection
  6. the verdict -- `classify_branch`, the single per-branch decision tree
"""

import json
import os
import re
import subprocess
import sys
from datetime import date, datetime
from typing import Dict, List, Sequence, Tuple

from util.config import (
    AFFECTED,
    ALREADY,
    MAINLINE_REF,
    NOT_AFFECTED,
    PREIMAGE_CACHE,
    REMOVED_LINES_CACHE,
    SUPPORTED_BRANCH_PREFIXES,
    UNSURE,
    VERSIONS_MANIFEST_PATH,
    is_test_or_generated_file,
    patch_id_pathspec,
)
from util.git import branch_basenames, changed_files_with_status, get_file_on_branch


# --------------------------------------------------------------------------
# 1. Text / line normalizers
# --------------------------------------------------------------------------


def norm_ws(s):
    """Collapse runs of whitespace so a reformatted line still matches."""
    return re.sub(r"\s+", " ", s).strip()


_C_FAMILY_EXT = (".c", ".cc", ".cpp", ".cxx", ".h", ".hpp", ".hh", ".hxx")


def is_c_file(file):
    """True for C/C++ source/headers, where '#' is a preprocessor directive
    (real code), not a comment."""
    return file is not None and file.lower().endswith(_C_FAMILY_EXT)


def is_noise_line(s, file=None):
    """True for lines with no vulnerable-code signal: comments, blanks, pure
    punctuation/braces. '#' is a comment only in non-C files; in C/C++ it is a
    preprocessor directive (real code) and is kept."""
    s = s.strip()
    if not s:
        return True
    if s.startswith(("//", "/*", "*/", "*")):  # C/C++ comments
        return True
    if s.startswith("#") and not is_c_file(file):  # script/config comment
        return True
    if set(s) <= set("{}();,: \t"):  # punctuation only
        return True
    return False


def is_boilerplate_line(s):
    """True for real-but-undistinctive lines (bare control-flow, #include, a lone
    string literal) that match too many files to be a reliable pre-image. Skipping
    them only weakens a match, so it is false-negative safe."""
    s = s.strip()
    if re.match(r"^(return|break|continue|goto)\b[^;{}]*;?$", s):
        return True
    if s.startswith("#include"):
        return True
    # Substance is only a string/char literal: strip quoted spans, require enough
    # remaining alnum to be distinctive.
    without_strings = re.sub(r'"(?:[^"\\]|\\.)*"|\'(?:[^\'\\]|\\.)*\'', "", s)
    if len(re.sub(r"\W", "", without_strings)) < 6:
        return True
    return False


# --------------------------------------------------------------------------
# 2. Vulnerable pre-image (are the fix's removed lines still on a branch?)
# --------------------------------------------------------------------------


def fix_removed_lines(commit, file):
    """The distinctive lines the fix removes/changes for *file* (the vulnerable
    pre-image), skipping comments, blanks, punctuation, and boilerplate."""
    cache_key = (commit, file)
    if cache_key in REMOVED_LINES_CACHE:
        return REMOVED_LINES_CACHE[cache_key]
    diff = subprocess.run(
        ["git", "diff", f"{commit}^", commit, "--", file],
        capture_output=True,
        text=True,
    )
    if diff.returncode != 0:
        REMOVED_LINES_CACHE[cache_key] = []
        return []
    removed = []
    for line in diff.stdout.splitlines():
        if line.startswith("-") and not line.startswith("---"):
            s = line[1:].strip()
            if is_noise_line(s, file):
                continue
            if is_boilerplate_line(s):
                continue
            if len(re.sub(r"\W", "", s)) >= 6:  # enough alnum to be distinctive
                removed.append(s)
    REMOVED_LINES_CACHE[cache_key] = removed
    return removed


def vulnerable_preimage_present(commit, changed_files, ref):
    """Whether the exact lines the fix removes/changes are still on *ref*:
    True  -> present (branch still vulnerable);
    False -> provably absent (code diverged or not here);
    None  -> the fix removes nothing distinctive (pure addition), can't tell.
    """
    cache_key = (commit, tuple(changed_files), ref)
    if cache_key in PREIMAGE_CACHE:
        return PREIMAGE_CACHE[cache_key]
    result = vulnerable_preimage_present_uncached(commit, changed_files, ref)
    PREIMAGE_CACHE[cache_key] = result
    return result


def vulnerable_preimage_present_uncached(commit, changed_files, ref):
    saw_removed = False
    for file in changed_files:
        # Skip test/generated files: a match there isn't the shipped vulnerable
        # code, and counting it produced false 'still present' (affected) results.
        if is_test_or_generated_file(file):
            continue
        removed = fix_removed_lines(commit, file)
        if not removed:
            continue
        saw_removed = True
        show = subprocess.run(
            ["git", "show", f"{ref}:{file}"], capture_output=True, text=True
        )
        if show.returncode != 0:
            continue
        content = norm_ws(show.stdout)
        for rl in removed:
            if norm_ws(rl) in content:
                return True
    if not saw_removed:
        return None
    return False


# --------------------------------------------------------------------------
# 3. Supported-branch resolution
# --------------------------------------------------------------------------


def remote_branch_names():
    """Branch names (without the `origin/` prefix) from `git branch -r`,
    skipping the symbolic `origin/HEAD -> origin/main` ref."""
    result = subprocess.run(["git", "branch", "-r"], capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"git branch -r failed: {result.stderr}")
    names = []
    for line in result.stdout.splitlines():
        line = line.strip()
        if " -> " in line or not line.startswith("origin/"):
            continue
        names.append(line[len("origin/") :])
    return names


def load_versions_manifest():
    """Load the FIPS branch manifest (`VERSIONS_MANIFEST_PATH`), or None if absent.

    Looks in the working tree first, then at the file as it exists on the mainline
    ref (so it still works from a feature branch). A present-but-malformed file
    logs a warning and returns None so we fall back to prefix matching.
    """
    text = None
    on_disk = os.path.join(os.getcwd(), VERSIONS_MANIFEST_PATH)
    if os.path.isfile(on_disk):
        try:
            with open(on_disk, encoding="utf-8") as fh:
                text = fh.read()
        except OSError:
            text = None
    if text is None:
        show = subprocess.run(
            ["git", "show", f"{MAINLINE_REF}:{VERSIONS_MANIFEST_PATH}"],
            capture_output=True,
            text=True,
        )
        if show.returncode == 0:
            text = show.stdout
    if not text or not text.strip():
        return None
    try:
        return json.loads(text)
    except json.JSONDecodeError as exc:
        print(
            f"[versions] {VERSIONS_MANIFEST_PATH} is present but not valid JSON "
            f"({exc}); falling back to branch-prefix matching.",
            file=sys.stderr,
        )
        return None


def parse_eos_date(value):
    """Parse an end-of-support date (`YYYY-MM-DD` or `YYYY-MM`). Returns None if
    missing/unparseable, which callers treat as "no known EOS" (still supported)."""
    for fmt in ("%Y-%m-%d", "%Y-%m"):
        try:
            return datetime.strptime((value or "").strip(), fmt).date()
        except ValueError:
            continue
    return None


def branch_support_status(today=None):
    """Per-branch support records derived from the manifest.

    Each record is the manifest entry plus `end_of_support_date`, `exists`
    (present as an origin/ ref), and `supported` (exists AND actively_maintained
    AND not past end_of_support as of `today`). Returns [] when no manifest.

    `today` is overridable so a historical replay can ask "was this branch in
    support as of the fix date?" rather than only "is it in support now?".
    """
    manifest = load_versions_manifest()
    if not manifest:
        return []
    today = today or date.today()
    remote = set(remote_branch_names())
    records = []
    for entry in manifest.get("fips_branches", []):
        name = entry.get("branch")
        if not name:
            continue
        eos = parse_eos_date(entry.get("end_of_support"))
        within_window = eos is None or eos >= today
        maintained = entry.get("actively_maintained", True)
        record = dict(entry)
        record["end_of_support_date"] = eos.isoformat() if eos else None
        record["exists"] = name in remote
        record["supported"] = bool(record["exists"] and maintained and within_window)
        records.append(record)
    return records


def branch_date_key(name):
    """The YYYY-MM-DD embedded in *name*, or '' if none. Used to order branches."""
    m = re.search(r"\d{4}-\d{2}-\d{2}", name)
    return m.group(0) if m else ""


def sort_branches(names):
    """Order branches newest -> oldest by the date in their name (undated last).
    The single source of truth for branch ordering, so every listing matches."""
    return sorted(
        names,
        key=lambda n: (branch_date_key(n) or "0000-00-00", n),
        reverse=True,
    )


def get_supported_branches(today=None):
    """Branch names (without `origin/`) to consider for backport, newest -> oldest.
    From the manifest when present (supported = exists as a ref, actively
    maintained, not past end-of-support), else branch-name prefix matching."""
    records = branch_support_status(today=today)
    if records:
        dropped = [r["branch"] for r in records if r["exists"] and not r["supported"]]
        if dropped:
            print(
                "[versions] skipping out-of-support branch(es) per "
                f"{VERSIONS_MANIFEST_PATH}: {', '.join(dropped)}",
                file=sys.stderr,
            )
        supported = [r["branch"] for r in records if r["supported"]]
    else:
        supported = [
            name
            for name in remote_branch_names()
            if f"origin/{name}".startswith(SUPPORTED_BRANCH_PREFIXES)
        ]
    return sort_branches(supported)


def get_changed_files(commit):
    """Files changed by the fix commit (vs. its parent)."""
    result = subprocess.run(
        ["git", "diff-tree", "--no-commit-id", "--name-only", "-r", commit],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        raise RuntimeError(f"git diff-tree failed: {result.stderr}")

    files = []

    for line in result.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        files.append(line)

    return files


# --------------------------------------------------------------------------
# 4. Introducer tracing
# --------------------------------------------------------------------------


def find_introducing_commit(commit, files):
    """Commit(s) that introduced the code the fix changes. For each touched line
    range, `git log -L --reverse` gives the oldest commit to write those lines
    (the introducer), falling back to `git blame -w -M -C`. Comment/blank/
    punctuation-only hunks are skipped so a stale comment can't trace to an
    ancient import. Returns a set of SHAs."""
    introducing = set()

    for file in files:
        # Test/generated files aren't the vulnerable source, and their introducer
        # would over-flag branches that lack the fixed module.
        if is_test_or_generated_file(file):
            continue
        result = subprocess.run(
            ["git", "diff", "-U0", f"{commit}^", commit, "--", file],
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            raise RuntimeError(f"git diff failed: {result.stderr}")

        # Parse each hunk with its changed lines so noise-only hunks can be skipped.
        hunks = []
        cur = None
        for line in result.stdout.splitlines():
            if line.startswith("@@"):
                match = re.match(r"^@@ -(\d+)(?:,(\d+))? ", line)
                cur = None
                if match:
                    cur = {
                        "start": int(match.group(1)),
                        "count": int(match.group(2)) if match.group(2) else 1,
                        "changed": [],
                    }
                    hunks.append(cur)
            elif (
                cur is not None
                and line
                and line[0] in "+-"
                and not line.startswith(("+++", "---"))
            ):
                cur["changed"].append(line[1:])

        for h in hunks:
            if h["changed"] and all(is_noise_line(c, file) for c in h["changed"]):
                continue  # comment/blank/punctuation-only change: not impact-relevant
            old_start, old_count = h["start"], h["count"]
            if old_count == 0:
                # Pure addition: inspect the line right after the insertion point.
                blame_start = old_start + 1
                blame_end = old_start + 1
            else:
                # Lines were removed/modified: inspect those exact lines.
                blame_start = old_start
                blame_end = old_start + old_count - 1

            origin_sha = find_line_origin(file, blame_start, blame_end, f"{commit}^")
            if origin_sha:
                introducing.add(origin_sha)

    return introducing


def find_line_origin(file, line_start, line_end, ref):
    """SHA of the oldest commit to touch lines [line_start, line_end] of *file* as
    of *ref* (via `git log -L --reverse`), falling back to `git blame -w -M -C`."""
    log_result = subprocess.run(
        [
            "git",
            "log",
            f"-L{line_start},{line_end}:{file}",
            "--format=%H",
            "--reverse",
            ref,
        ],
        capture_output=True,
        text=True,
    )
    if log_result.returncode == 0:
        for log_line in log_result.stdout.splitlines():
            log_line = log_line.strip()
            # `--format=%H` only prints SHAs on their own lines; the rest is the
            # diff body. Take the first 40-char hex string we see.
            if len(log_line) == 40 and all(c in "0123456789abcdef" for c in log_line):
                return log_line

    # Fallback: use blame (with whitespace/move-aware flags). Less accurate for
    # finding the original introducer, but works on edge cases log -L can't.
    blame_result = subprocess.run(
        [
            "git",
            "blame",
            "-w",
            "-M",
            "-C",
            "-L",
            f"{line_start},{line_end}",
            ref,
            "--",
            file,
        ],
        capture_output=True,
        text=True,
    )
    if blame_result.returncode != 0:
        # Both failed -- usually a pure addition whose post-insertion line is at/past
        # EOF in the parent (newly-added lines have no pre-image). Skip this hunk.
        print(
            f"[introducer] no pre-image for {file}:{line_start}-{line_end} on "
            f"{ref} (likely newly-added lines); skipping this hunk.",
            file=sys.stderr,
        )
        return None
    for blame_line in blame_result.stdout.splitlines():
        if not blame_line:
            continue
        return blame_line.split()[0].lstrip("^")
    return None


# --------------------------------------------------------------------------
# 5. Ancestry / patch-id reachability and already-patched detection
# --------------------------------------------------------------------------


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


# --------------------------------------------------------------------------
# 5b. Already-patched detection
# --------------------------------------------------------------------------


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
    log = subprocess.run(
        ["git", "log", "--format=%B%x00", f"{MAINLINE_REF}..{ref}"],
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
    rev_range = f"{MAINLINE_REF}..{ref}"
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


# --------------------------------------------------------------------------
# 6. The per-branch verdict
# --------------------------------------------------------------------------


def classify_branch(
    fix_sha: str, src_files: Sequence[str], introducers, branch: str
) -> str:
    """The single deterministic verdict for one branch: AFFECTED / NOT_AFFECTED /
    UNSURE / ALREADY.

    This is the ONE implementation of the decision tree -- the CLI reaches it via
    :func:`analyze_branches`, and the replay bench calls it directly, so the
    scorecard grades exactly the logic that ships.

    Safety stance: a branch is only ever called NOT AFFECTED when we are confident
    the changed code is absent. If ancestry/patch-id do not match but the file is
    present (or a same-named file exists under a path we could not trace), the
    branch is escalated to UNSURE rather than risk a silent false negative.
    """
    ref = f"origin/{branch}"
    # The fix is ALREADY on this branch -- as a direct ancestor (the branch forked
    # after the fix landed), a `-x` cherry-pick annotation naming its exact SHA, or
    # a matching patch-id. Nothing to backport, whatever the pre-image says.
    #
    # This has to come first: an applied fix REMOVES the vulnerable lines, so the
    # pre-image is provably absent on precisely these branches. Checking it further
    # down (gated on `preimage is not False`) meant the check could never fire when
    # it mattered, and every already-patched branch fell through to UNSURE -- i.e.
    # got re-flagged for a backport it already has.
    if is_already_patched(fix_sha, branch):
        return ALREADY
    # Path 1 + Path 2: does an introducer reach the branch by SHA ancestry or
    # patch-id equivalence?
    affected = introducer_reaches(introducers, ref)
    # Corroborate ancestry/patch-id with the vulnerable pre-image. The
    # oldest-introducer heuristic flags a branch as soon as ONE introducer
    # reaches it, which over-flags when that introducer is old shared code the
    # fix also touched. `vulnerable_preimage_present` is the tiebreaker:
    #   True  -> the exact lines the fix removes are still here (real hit)
    #   None  -> pure-addition fix, nothing to check (trust ancestry)
    #   False -> those lines are provably absent (ancestry matched old shared
    #            code) -> NOT a confident AFFECTED; fall through to UNSURE so
    #            the AI decides (and it is flagged for review under --no-ai,
    #            never a silent miss).
    preimage = vulnerable_preimage_present(fix_sha, src_files, ref)
    if affected and preimage is not False:
        return AFFECTED
    # Path 2b: ancestry/patch-id missed (a branch-specific introducer), but the
    # exact removed lines ARE present -> deterministically AFFECTED.
    if not affected and preimage is True:
        return AFFECTED
    # Not confidently affected. Decide UNSURE vs a confident NOT AFFECTED,
    # biasing hard toward UNSURE so a miss is never silent.
    present = any(
        get_file_on_branch(f, ref, commit=fix_sha)[0] is not None for f in src_files
    )
    if not present:
        # Conservative guard: if the rename-aware lookup found nothing but a
        # file with the same name exists elsewhere on the branch, the code
        # may be there under a path we could not trace. Escalate to UNSURE
        # rather than declare a confident (and possibly false) NOT AFFECTED.
        basenames = branch_basenames(ref)
        if any(os.path.basename(f) in basenames for f in src_files):
            present = True
    return UNSURE if present else NOT_AFFECTED


def source_files(files: Sequence[str]) -> "List[str]":
    """The shipped-source subset of *files* that impact is judged on.

    A co-changed *_test.cc / generated file must never make a branch affected (its
    presence, or a stale line in it, is not the vulnerable code). Falls back to all
    files only if the fix is test/generated-only.
    """
    return [f for f in files if not is_test_or_generated_file(f)] or list(files)


def analyze_branches(
    fix_sha: str, branches: Sequence[str]
) -> "Tuple[List[str], List[str], Dict[str, str]]":
    """Classify each branch deterministically (no AI).

    Returns ``(changed_files, sorted_introducers, buckets)``, where buckets maps
    each branch to one of AFFECTED / NOT_AFFECTED / UNSURE / ALREADY. The per-branch
    decision lives in :func:`classify_branch`.
    """
    files, introducer_files = changed_files_with_status(fix_sha)
    introducers = find_introducing_commit(fix_sha, introducer_files)
    src_files = source_files(files)
    buckets = {
        branch: classify_branch(fix_sha, src_files, introducers, branch)
        for branch in branches
    }
    return files, sorted(introducers), buckets
