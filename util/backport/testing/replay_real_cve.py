"""
Replay a real, previously hand-backported AWS-LC fix and check whether our tool's
branch analysis matches what the team actually did by hand.

WHAT IT DOES
------------
Given a fix commit that already landed on aws/aws-lc mainline, for each supported
release branch this harness:

  1. Discovers the GROUND TRUTH (which branches the humans actually backported the
     fix to) directly from the real repo, using two independent signals:
       - `git cherry-pick -x` annotations ("cherry picked from commit <sha>")
       - patch-id equivalence of a divergent commit on the branch
  2. Rolls the repo back to the state right before that hand-made backport landed
     (for affected branches, the branch is reset to the backport commit's parent),
     so the fix is genuinely absent again and the tool has to rediscover the need.
  3. Runs the REAL deterministic engine (src/engine.py) against that rolled-back
     world (get_changed_files -> find_introducing_commit -> is_branch_affected ->
     is_already_patched, and optionally a cherry-pick apply).
  4. Compares the tool's per-branch verdict to the ground truth and scores it
     (true/false positive/negative), printing a table + scorecard per fix.

SAFETY
------
This never mutates your real repo and never pushes or calls `gh`. It builds a
throwaway sandbox repo that borrows the real repo's object store read-only via git
`alternates`, then creates/rewrites refs only inside that sandbox. The real repo is
only ever read.

USAGE
-----
    # (run from the util/backport dir). The curated bench, scored vs the key:
    python3 testing/replay_real_cve.py --file testing/reliable_cves.txt \
        --answers testing/answer_key.txt

    # Replay specific fix commits (SHAs or refs on mainline):
    python3 testing/replay_real_cve.py 9545d9de6059 110f184623b5

    # Replay by PR / merge number (resolved from mainline commit subjects):
    python3 testing/replay_real_cve.py 1109 '#1917'

    # AI is ON by default (mirrors how the bot runs). Add --no-ai for an
    # offline / no-creds deterministic-only sweep (ground truth is unchanged):
    python3 testing/replay_real_cve.py --file testing/reliable_cves.txt --no-ai

    # Also attempt the cherry-pick apply (slower: checks out each branch):
    python3 testing/replay_real_cve.py --cherry-pick

    # Point at a different clone, or limit branches:
    python3 testing/replay_real_cve.py --repo /path/to/aws-lc \
        --branches fips-2024-09-27 fips-2025-09-12-lts

    # Override the discovered ground truth (comma-separated affected branches):
    python3 testing/replay_real_cve.py 9545d9de6059 --truth fips-2022-11-02,fips-2021-10-20

Set KEEP_SANDBOX=1 to leave the throwaway repos on disk for inspection.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor
from contextlib import contextmanager
from datetime import datetime
from pathlib import Path

# The engine lives in the src/ folder one directory up; import from there.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))
from ai import ai_client  # noqa: E402
from engine import (  # noqa: E402
    is_test_or_generated_file,
    parse_eos_date,
    patch_id_pathspec,
    find_introducing_commit,
    get_changed_files,
    is_already_patched,
    is_branch_affected,
    vulnerable_preimage_present,
)

DEFAULT_REPO = os.environ.get("AWS_LC_REPO", "/Users/tianyiy/aws-lc")

# Support-window manifest for the real aws-lc branches (derived from VERSIONING.md).
# Lives next to this repo; the replay drops branches that are out of support as of
# a fix's date so the tool is never scored for skipping an EOL branch.
DEFAULT_VERSIONS = str(Path(__file__).resolve().parent / "fips_versions.aws-lc.json")

# The real supported release branches (oldest -> newest, one-off last).
DEFAULT_BRANCHES = [
    "fips-2021-10-20",
    "fips-2021-10-20-1MU",
    "fips-2022-11-02",
    "fips-NetOS-2024-06-11",
    "fips-2024-09-27",
    "fips-2025-09-12-lts",
]

# Real, previously hand-backported mainline fixes, verified to exist on aws/aws-lc
# and to have been cherry-picked to more than one branch. Ground truth is still
# discovered from the repo at run time; these are just convenient defaults that
# exercise real multi-branch discrimination.
BUILTIN_EXAMPLES = [
    ("e17506cdbde1", "pkcs8: cap ciphertext length before allocating"),
    ("9545d9de6059", "Fix DH_check() excessive time with oversized modulus (#1109)"),
    ("110f184623b5", "Reject XOF digests in DH_compute_key_hashed"),
    ("921c6465918e", "1-byte OOB read in EVP_PKEY_asn1_find_str length calc"),
]

_CHERRY_X = re.compile(r"cherry picked from commit ([0-9a-f]{7,40})", re.I)

# A mainline PR number, e.g. "(#3270)" in a fix subject. Hand-backports very often
# reference the ORIGINAL PR in their own subject/body (e.g.
# "[CHERRYPICK FIPS 3.x] ... (#3270) (#3273)" or "Cherrypick of #3270 onto ...")
# while carrying NO `cherry picked from commit <sha>` line and, because the older
# branch context differs, no matching patch-id. Signals 1 and 2 miss those; the
# PR-reference signal below catches them.
_PR_RE = re.compile(r"#(\d{2,6})")
_BACKPORT_KW = re.compile(r"cherry.?pick|backport", re.I)

# CVE identifiers, used to link a mainline fix to a REIMPLEMENTED backport that
# shares no patch-id and doesn't -x-reference the mainline commit (a hand-rewrite
# for older branch code). Both the mainline commit message and the branch's
# backport commit usually name the same CVE, so it's a reliable cross-branch key.
# Ground-truth measurement only — a message-string match is deliberately NOT used
# to let the bot skip a backport (that would risk a false negative).
_CVE_RE = re.compile(r"CVE-\d{4}-\d{4,7}", re.I)


def extract_cves(text):
    return {m.upper() for m in _CVE_RE.findall(text or "")}


def norm_subject(s):
    """Normalize a commit subject for backport matching: drop the trailing PR
    number "(#NNNN)" and lowercase. AWS-LC backport PRs typically reuse the exact
    mainline title with only a new PR number, so the normalized subjects match."""
    s = (s or "").strip()
    s = re.sub(r"\s*\(#\d+\)\s*$", "", s)
    return s.strip().lower()


# Serializes the cherry-pick worktree lifecycle (git worktree add/remove/prune
# mutate .git/worktrees and are not safe to run concurrently in one repo).
_WT_LOCK = threading.Lock()


# ---------------------------------------------------------------------------
# Git helpers (all read-only against the real repo)
# ---------------------------------------------------------------------------


def git(cwd, *args, check=True):
    proc = subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True)
    if check and proc.returncode != 0:
        raise RuntimeError(
            f"git {' '.join(args)} failed in {cwd}:\n{proc.stdout}\n{proc.stderr}"
        )
    return proc


def rev_parse(repo, ref):
    r = git(repo, "rev-parse", "--verify", "--quiet", ref, check=False)
    return r.stdout.strip() or None


def subject(repo, sha):
    return git(repo, "log", "-1", "--format=%s", sha, check=False).stdout.strip()


def resolve_pr_number(repo, n, mainline="origin/main"):
    """
    Resolve a PR/merge number to the mainline commit that carried it, by searching
    commit subjects. AWS-LC squash-merges with the number appended as "(#N)";
    older merge-commit style is "Merge pull request #N from ...". Prefers a subject
    that ends with "(#N)", falls back to any subject containing it, then to a merge
    commit. Returns the most recent match, or None.
    """
    out = git(
        repo,
        "log",
        mainline,
        f"--grep=(#{n})",
        "--fixed-strings",
        "--format=%H%x1f%s",
        check=False,
    ).stdout
    contains = []
    for line in out.splitlines():
        if "\x1f" in line:
            h, s = line.split("\x1f", 1)
            contains.append((h.strip(), s))
    exact = [(h, s) for h, s in contains if s.rstrip().endswith(f"(#{n})")]
    pool = exact or contains
    if not pool:
        out2 = git(
            repo,
            "log",
            mainline,
            f"--grep=Merge pull request #{n} ",
            "--format=%H%x1f%s",
            check=False,
        ).stdout
        for line in out2.splitlines():
            if "\x1f" in line:
                h, s = line.split("\x1f", 1)
                pool.append((h.strip(), s))
    if not pool:
        return None
    if len(pool) > 1:
        print(
            f"[warn] #{n}: {len(pool)} candidate commits on {mainline}; using the most "
            f'recent ({pool[0][0][:12]} "{pool[0][1][:50]}")',
            file=sys.stderr,
        )
    return pool[0][0]


def resolve_ref(repo, token):
    """
    Resolve a user-supplied token to a mainline commit SHA. Accepts either a git
    SHA/ref, or a PR/merge number like '1109' or '#1109' (resolved by searching
    mainline commit subjects; see resolve_pr_number).
    """
    stripped = token.lstrip("#").strip()
    if stripped.isdigit():
        return resolve_pr_number(repo, stripped)
    return rev_parse(repo, token)


def read_commits_file(path):
    """Read fix commits / PR-numbers to replay, one per line.

    Format: one token per line (a SHA, a ref, or a PR number like `1109` or
    `#1109`), with an optional free-text label after whitespace. Blank lines and
    comments are ignored; a comment is a line starting with `//` or with `#`
    followed by a non-digit (so `# note` is a comment but `#1917` is still a PR
    number).
    """
    entries = []
    try:
        with open(path, encoding="utf-8") as fh:
            for raw in fh:
                line = raw.strip()
                if not line or line.startswith("//"):
                    continue
                if line.startswith("#") and (len(line) < 2 or not line[1].isdigit()):
                    continue  # comment, not a '#<number>' PR reference
                parts = line.split(None, 1)
                token = parts[0]
                label = parts[1].strip() if len(parts) > 1 else None
                entries.append((token, label))
    except OSError as exc:
        print(f"[error] cannot read --file {path}: {exc}", file=sys.stderr)
    return entries


def load_versions(path):
    """Load the support-window manifest (fips_versions.json shape), or None."""
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return None


def commit_date(repo, sha):
    """Committer date of a commit as a datetime.date (for support-window checks)."""
    out = git(repo, "log", "-1", "--format=%cs", sha, check=False).stdout.strip()
    try:
        return datetime.strptime(out, "%Y-%m-%d").date()
    except ValueError:
        return None


def filter_by_support_window(manifest, branches, as_of):
    """Split *branches* into (in_support, dropped) as of the date *as_of*.

    A branch is out of support when its manifest entry is not actively maintained
    or its end_of_support date is before *as_of*. Branches absent from the
    manifest are kept (unknown = don't silently drop). *dropped* is a list of
    (branch, reason) pairs. When there's no manifest or no date, nothing drops.
    """
    if not manifest or as_of is None:
        return list(branches), []
    entries = {e.get("branch"): e for e in manifest.get("fips_branches", [])}
    in_support, dropped = [], []
    for b in branches:
        e = entries.get(b)
        if e is None:
            in_support.append(b)
            continue
        if not e.get("actively_maintained", True):
            dropped.append((b, "not actively maintained"))
            continue
        eos = parse_eos_date(e.get("end_of_support"))
        if eos is not None and eos < as_of:
            dropped.append((b, f"end of support {e.get('end_of_support')} < fix date"))
            continue
        in_support.append(b)
    return in_support, dropped


@contextmanager
def chdir(path):
    prev = os.getcwd()
    os.chdir(path)
    try:
        yield
    finally:
        os.chdir(prev)


# ---------------------------------------------------------------------------
# Ground-truth discovery (what the humans actually backported)
# ---------------------------------------------------------------------------


def patch_id_map(repo, rev_range):
    """Return {patch_id: commit_sha} for the commits in rev_range (read as bytes).

    Patch-ids exclude auto-generated/derived files (same pathspec the bot uses),
    so a reshaped backport whose only difference from the mainline fix is a
    regenerated tree still matches — otherwise the ground truth would miss it and
    mislabel an already-backported branch as "not patched"."""
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
        cwd=repo,
        capture_output=True,
    )
    if log.returncode != 0:
        return {}
    pid = subprocess.run(
        ["git", "patch-id", "--stable"], input=log.stdout, cwd=repo, capture_output=True
    )
    out = pid.stdout.decode("ascii", errors="replace")
    mapping = {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) >= 2:
            mapping[parts[0]] = parts[1]
    return mapping


def discover_ground_truth(repo, fix_sha, branches, label=None):
    """
    Determine, per branch, whether the fix was hand-backported and if so to which
    commit (used as the rollback point). Combines cherry-pick -x annotations and
    patch-id equivalence; either signal is sufficient.

    Returns {branch: {"affected": bool, "backport": sha|None, "via": str}}.
    """
    fix_pid_map = patch_id_map(repo, f"{fix_sha}^..{fix_sha}")
    fix_pid = next(iter(fix_pid_map), None)  # patch-id of the fix itself
    fix_short = fix_sha[:12]

    # CVE ids the fix addresses, taken from the commit message AND the test-file
    # label (many mainline commits don't name the CVE, but the list entry does).
    fix_msg = git(repo, "log", "-1", "--format=%B", fix_sha, check=False).stdout
    cve_ids = extract_cves(fix_msg) | extract_cves(label)

    # PR number(s) from the fix SUBJECT only (the trailing "(#NNNN)"). Used to link
    # a mainline fix to a separate-PR hand-backport that cites it (Signal 1b).
    fix_subject = git(repo, "log", "-1", "--format=%s", fix_sha, check=False).stdout
    fix_prs = set(_PR_RE.findall(fix_subject))
    fix_title = norm_subject(fix_subject)

    # Changed source files, used by the pre-image presence check (Signal 4). Its
    # git queries are cwd-relative, so run them in the target repo.
    with chdir(repo):
        changed_files = get_changed_files(fix_sha)

    result = {}
    for b in branches:
        ref = f"origin/{b}"
        rng = f"origin/main..{ref}"
        via = []
        backport = None

        # Signal 0: the fix commit is a direct ANCESTOR of the branch (the branch
        # forked AFTER the fix landed on mainline), so it already contains the fix
        # through shared history and never needed a backport. This is distinct
        # from a hand-backport, and the divergent-only signals below can't see it,
        # so without this check such a branch is mislabeled "not patched".
        anc = subprocess.run(
            ["git", "merge-base", "--is-ancestor", fix_sha, ref],
            cwd=repo,
            capture_output=True,
        )
        already_present = anc.returncode == 0
        if already_present:
            via.append("ancestor")

        # Signal 1: cherry-pick -x annotation referencing the fix commit. The log
        # carries subject + body so both -x lines (body) and CVE ids (usually the
        # subject) are visible.
        log = git(repo, "log", rng, "--format=%H%x1f%s%n%b%x1e", check=False).stdout
        entries = []
        for entry in log.split("\x1e"):
            if "\x1f" not in entry:
                continue
            h, text = entry.split("\x1f", 1)
            entries.append((h.strip(), text))
            for m in _CHERRY_X.finditer(text):
                if fix_sha.startswith(m.group(1)) or m.group(1).startswith(fix_short):
                    if backport is None:
                        backport = h.strip()
                    if "-x" not in via:
                        via.append("-x")
                    break

        # Signal 2: a divergent commit with the same patch-id as the fix.
        if fix_pid:
            branch_pids = patch_id_map(repo, rng)
            if fix_pid in branch_pids:
                if backport is None:
                    backport = branch_pids[fix_pid]
                via.append("patch-id")

        # Signal 1b: a divergent commit that cites the fix's ORIGINAL PR number
        # together with a cherry-pick/backport keyword (e.g.
        # "[CHERRYPICK FIPS 3.x] ... (#3270) (#3273)" or "Cherrypick of #3270").
        # These hand-backports frequently carry NO `cherry picked from commit`
        # line and, because the older branch context differs, NO matching
        # patch-id -- so Signals 1 and 2 miss them. It is a real backport and a
        # clean rollback point (a single cherry-pick commit we can reset before).
        if backport is None and fix_prs:
            for h, text in entries:
                if _BACKPORT_KW.search(text) and any(
                    re.search(r"#" + re.escape(pr) + r"(?!\d)", text) for pr in fix_prs
                ):
                    backport = h
                    if "pr-ref" not in via:
                        via.append("pr-ref")
                    break

        # Signal 1c: a divergent commit whose SUBJECT matches the fix's subject
        # (ignoring the trailing "(#NNNN)"). AWS-LC backport PRs very often reuse
        # the exact mainline title with only a new PR number -- e.g.
        # "Fix CN fallback handling in name constraints checking (#3108)" backports
        # "... (#3107)" -- so they cite a DIFFERENT PR (Signal 1b misses it) and,
        # with older branch context, carry no matching patch-id (Signal 2 misses
        # it). This is a real backport and a clean rollback point.
        if backport is None and fix_title:
            for h, text in entries:
                if norm_subject(text.split("\n", 1)[0]) == fix_title:
                    backport = h
                    if "same-title" not in via:
                        via.append("same-title")
                    break

        # Signal 3: a divergent commit names the same CVE id(s). Catches
        # REIMPLEMENTED backports (hand-rewritten for older code) that share no
        # patch-id and don't -x-reference the mainline commit — the exact case
        # patch-id and -x miss. Recorded as "already present" (the fix is there,
        # so no PR is needed) rather than a rollback point, because a reimplemented
        # or bundled commit is not a clean parent to reset to.
        cve_hit = False
        if cve_ids and backport is None:
            for _h, text in entries:
                if extract_cves(text) & cve_ids:
                    cve_hit = True
                    break
        if cve_hit:
            already_present = True
            if "cve-id" not in via:
                via.append("cve-id")

        # Signal 4: no shipped backport was found, but the vulnerable code the fix
        # targets is STILL PRESENT on the branch -- the exact lines the fix
        # removes (whitespace- and comment-normalized; test/generated files and
        # boilerplate excluded) are on the branch and the fix is not applied. The
        # branch IS affected in reality even though the team hasn't (yet) shipped a
        # backport: "affected" means the vulnerable code is present, not merely
        # that a backport was cut. There is no clean single-commit rollback point
        # (nothing was applied here), so the branch's real tip is analyzed as-is.
        preimage_affected = False
        if backport is None and not already_present and changed_files:
            with chdir(repo):
                if vulnerable_preimage_present(fix_sha, changed_files, ref) is True:
                    preimage_affected = True
                    if "preimage" not in via:
                        via.append("preimage")

        result[b] = {
            # "affected" = the branch should be flagged after rollback: EITHER a
            # hand-backport of this commit was found (-x / patch-id / PR-ref /
            # same-title) OR the vulnerable pre-image is still present (Signal 4).
            # Branches that merely already contain the fix (forked-after, or a
            # reimplementation matched by CVE id) set already_present instead.
            "affected": backport is not None or preimage_affected,
            "backport": backport,
            "already_present": already_present,
            "via": "+".join(dict.fromkeys(via)) if via else "",
        }
    return result


# ---------------------------------------------------------------------------
# Sandbox construction (throwaway repo borrowing real objects via alternates)
# ---------------------------------------------------------------------------


def build_sandbox(repo, fix_sha, ground_truth, branches):
    """
    Create a throwaway repo whose refs reproduce the pre-backport world:
      - origin/main is pinned to the fix commit (the world as of the merge)
      - each affected branch is rolled back to the parent of its hand-made backport
      - each unaffected branch keeps its real tip
    The sandbox borrows the real repo's objects read-only via alternates.
    """
    sandbox = tempfile.mkdtemp(prefix="awslc-cve-replay-")
    git(sandbox, "init", "-q", "-b", "main")
    alt = Path(sandbox, ".git", "objects", "info", "alternates")
    alt.write_text(str(Path(repo, ".git", "objects").resolve()) + "\n")

    git(sandbox, "update-ref", "refs/remotes/origin/main", fix_sha)

    rollbacks = {}
    for b in branches:
        gt = ground_truth[b]
        if gt["affected"] and gt["backport"]:
            parent = rev_parse(repo, f"{gt['backport']}^")
            target = parent or rev_parse(repo, f"origin/{b}")
            rollbacks[b] = parent
        else:
            target = rev_parse(repo, f"origin/{b}")
        if target:
            git(sandbox, "update-ref", f"refs/remotes/origin/{b}", target)
    return sandbox, rollbacks


def simulate_cherry_pick(sandbox, commit, branch):
    """Attempt the cherry-pick onto origin/<branch> in a throwaway worktree."""
    parent = tempfile.mkdtemp(prefix="cve-cp-")
    worktree = os.path.join(parent, "wt")
    try:
        add = git(
            sandbox,
            "worktree",
            "add",
            "--detach",
            worktree,
            f"origin/{branch}",
            check=False,
        )
        if add.returncode != 0:
            return "error"
        pick = git(worktree, "cherry-pick", commit, check=False)
        if pick.returncode == 0:
            return "clean"
        combined = (pick.stdout + pick.stderr).lower()
        if "empty" in combined or "nothing to commit" in combined:
            return "empty"
        # A conflict confined to test/generated files means the source fix applied
        # cleanly; the tool drops those hunks and finishes, so it's effectively a
        # clean backport. Report it separately from a real source conflict.
        status = git(worktree, "status", "--porcelain", check=False).stdout
        unmerged = []
        for line in status.splitlines():
            xy, path = line[:2], line[3:].strip()
            if "U" in xy or xy in ("AA", "DD"):
                unmerged.append(path)
        if unmerged and all(is_test_or_generated_file(p) for p in unmerged):
            return "test-only"
        return "conflict"
    finally:
        git(worktree, "cherry-pick", "--abort", check=False)
        git(sandbox, "worktree", "remove", "--force", worktree, check=False)
        shutil.rmtree(parent, ignore_errors=True)
        git(sandbox, "worktree", "prune", check=False)


# ---------------------------------------------------------------------------
# Engine run + scoring
# ---------------------------------------------------------------------------


def run_engine(sandbox, fix_sha, branches, do_cherry_pick, jobs=6):
    """Run the real deterministic engine in the sandbox; return per-branch verdicts.

    Branches are analyzed concurrently (up to *jobs* threads). This is the big win
    when AI is on, where each branch is an independent Bedrock call; git reads on
    the shared sandbox are safe concurrently, and the cherry-pick worktree
    lifecycle (which mutates .git/worktrees) is serialized with a lock.
    """
    with chdir(sandbox):
        files = get_changed_files(fix_sha)
        introducers = find_introducing_commit(fix_sha, files)

        def analyze(b):
            # Deterministic short-circuit FIRST (mirrors the real bot): if the fix
            # is already present on the branch (forked after the fix -> direct
            # ancestor, or a cherry-pick with a matching patch-id), no backport is
            # needed. Deciding this before impact analysis / AI makes the verdict
            # robust and independent of the AI auditor.
            if is_already_patched(fix_sha, b):
                return b, {
                    "backport": False,
                    "reason": "already_patched",
                    "cherry_pick": "",
                    "fix_already_ancestor": True,
                    "ai": None,
                    "preimage": vulnerable_preimage_present(
                        fix_sha, files, f"origin/{b}"
                    ),
                }

            affected, advisory = is_branch_affected(
                introducers, b, commit=fix_sha, changed_files=files
            )
            overrode = bool(advisory and advisory.get("overrode_deterministic"))
            reason, cp = "not_affected", ""
            if affected:
                if is_already_patched(fix_sha, b):
                    affected, reason = False, "already_patched"
                else:
                    reason = "ai_upgraded" if overrode else "needs_backport"
                    if do_cherry_pick:
                        with _WT_LOCK:  # worktree bookkeeping isn't concurrency-safe
                            cp = simulate_cherry_pick(sandbox, fix_sha, b)
                        if cp == "empty":
                            # git itself reports the change is already present
                            # (applied via a reshaped commit that ancestry and
                            # patch-id missed). Authoritative and FN-safe.
                            affected, reason = False, "already_patched(no-op)"
            elif overrode:
                reason = "ai_suppressed"
            elif advisory is not None:
                reason = "not_affected_ai"

            fix_ancestor = (
                git(
                    sandbox,
                    "merge-base",
                    "--is-ancestor",
                    fix_sha,
                    f"origin/{b}",
                    check=False,
                ).returncode
                == 0
            )
            return b, {
                "backport": affected,  # would the bot open a PR?
                "reason": reason,
                "cherry_pick": cp,
                "fix_already_ancestor": fix_ancestor,
                "ai": advisory,
                # For classifying false positives: is the vulnerable pre-image
                # actually on the branch? True = genuinely affected (not shipped),
                # False = provably absent (a true over-flag / tool error),
                # None = pure addition, can't tell from the pre-image.
                "preimage": vulnerable_preimage_present(fix_sha, files, f"origin/{b}"),
            }

        verdicts = {}
        with ThreadPoolExecutor(
            max_workers=max(1, min(jobs, len(branches) or 1))
        ) as ex:
            for b, v in ex.map(analyze, branches):
                verdicts[b] = v
        return files, introducers, verdicts


def classify(bot_backport, truth_affected):
    if bot_backport and truth_affected:
        return "TP"
    if bot_backport and not truth_affected:
        return "FP"
    if not bot_backport and truth_affected:
        return "FN"
    return "TN"


def format_scenario(
    repo,
    fix_sha,
    label,
    files,
    introducers,
    gt,
    rollbacks,
    verdicts,
    branches,
    sla_days=0,
    forked_after=frozenset(),
):
    """Build the per-fix report as a single string and return (text, labels)."""
    # Is this fix too recent to expect a hand-backport yet? An affected branch
    # that simply hasn't been backported within the SLA window is "pending", not
    # a false positive — the bot is right that it's affected.
    recent = False
    if sla_days and sla_days > 0:
        fdate = commit_date(repo, fix_sha)
        # Reference "now" = the mainline HEAD date (the repo's current state),
        # not wall-clock: this is a historical replay, so "has the team had time
        # to backport?" is measured against how far mainline has moved since the
        # fix, which is stable and reproducible. Falls back to wall-clock.
        ref_date = commit_date(
            repo, os.environ.get("BACKPORT_MAINLINE_REF", "origin/main")
        )
        if ref_date is None:
            ref_date = datetime.now().date()
        if fdate is not None:
            recent = (ref_date - fdate).days < sla_days

    out = []
    out.append(f"\n{'=' * 104}")
    out.append(f"{label}")
    out.append(f'  fix commit: {fix_sha[:12]}   "{subject(repo, fix_sha)}"')
    out.append(f"{'=' * 104}")
    out.append(f"  changed files: {files}")
    out.append(f"  introducer(s): {sorted(s[:10] for s in introducers)}")
    out.append("")
    out.append(
        f"  {'branch':<24} {'bot verdict':<12} {'reason':<16} {'cherry':<8} "
        f"{'manual outcome':<16} {'gt via':<10} {'match'}"
    )
    out.append(
        f"  {'-' * 24} {'-' * 12} {'-' * 16} {'-' * 8} {'-' * 16} {'-' * 10} {'-' * 6}"
    )

    labels = []
    notes = []
    for b in branches:
        v = verdicts[b]
        truth = gt[b]["affected"]
        lbl = classify(v["backport"], truth)
        _ai = v.get("ai") or {}
        ai_upgraded = bool(
            _ai.get("overrode_deterministic") and _ai.get("likely_affected") is True
        )
        reimpl = bool(gt[b].get("already_present") and "cve-id" in gt[b].get("via", ""))
        labels.append((lbl, v.get("preimage"), ai_upgraded, reimpl, recent))

        bot_str = "BACKPORT" if v["backport"] else "skip"
        gvia = gt[b].get("via", "")
        manual_key = "manual" in gvia
        if truth:
            # affected = should be flagged after rollback. In answer-key mode this is
            # our hand-verified call; in auto mode it means the code is vulnerable
            # here -- either the team shipped a backport, or the vulnerable
            # pre-image is still present (Signal 4).
            if manual_key:
                manual = "AFFECTED"
            elif any(s in gvia for s in ("-x", "patch-id", "pr-ref", "same-title")):
                manual = "AFFECTED (backport)"
            else:
                manual = "AFFECTED (code)"
        elif b in forked_after:
            # forked from main AFTER the fix -> born with it; inherited, NOT backported
            manual = "has fix (forked-after)"
        elif gt[b].get("already_present"):
            if "cve-id" in gvia:
                manual = "has fix (cve)"
            elif "ancestor" in gvia:
                manual = "has fix (forked-after)"
            else:
                manual = "has fix"
        else:
            manual = "not affected"
        ok = "OK" if lbl in ("TP", "TN") else f"{lbl} <-"
        if lbl == "FP":
            # A bot BACKPORT that the team never *shipped* isn't automatically an
            # error. Relabel by WHY, so correct-but-unshipped flags don't read as
            # tool false positives:
            if gt[b].get("already_present") and "cve-id" in gvia:
                ok = "redundant"  # already patched via a reimplementation
            elif v.get("preimage") is True:
                ok = "AFFECTED*"  # vulnerable code present, team hasn't backported yet
            elif v.get("preimage") is False:
                _ai2 = v.get("ai") or {}
                ok = (
                    "ai-flag?" if _ai2.get("overrode_deterministic") else "OVER-FLAG <-"
                )
            else:
                ok = "addn?"  # pure-addition, can't judge from pre-image
        out.append(
            f"  {b:<24} {bot_str:<12} {v['reason']:<16} {v['cherry_pick']:<8} "
            f"{manual:<16} {gt[b]['via']:<10} {ok}"
        )
        if lbl == "FP" and gt[b].get("already_present") and "cve-id" in gvia:
            notes.append(
                f"    - {b}: redundant over-flag — the fix is already present as a "
                f"REIMPLEMENTED backport (matched by CVE id, shares no patch-id, so "
                f"the bot can't detect it). The bot would open a redundant PR a human "
                f"closes; NOT a missed backport."
            )
        elif lbl == "FP" and v.get("preimage") is False:
            ai = v.get("ai") or {}
            if ai.get("overrode_deterministic") and ai.get("likely_affected") is True:
                notes.append(
                    f"    - {b}: pre-image ABSENT (exact patched lines are not on this "
                    f"branch, so deterministic said INCONCLUSIVE) but the AI tie-breaker "
                    f"UPGRADED to affected -> NOT a deterministic error: verify the AI's "
                    f"call (older code may still be vulnerable via different lines)."
                )
            else:
                notes.append(
                    f"    - {b}: *** TRUE OVER-FLAG *** vulnerable pre-image provably "
                    f"ABSENT and AI did not upgrade -> likely a genuine tool error "
                    f"worth double-checking."
                )
        elif lbl == "FP" and v["fix_already_ancestor"]:
            notes.append(
                f"    - {b}: false positive, but the fix is already an ancestor of "
                f"this branch (already patched via shared history; is_already_patched's "
                f"divergent-only scan missed it)."
            )
        elif lbl == "FP" and v.get("preimage") is True:
            notes.append(
                f"    - {b}: FP (not a tool error): vulnerable code IS present, but the "
                f"team hasn't shipped this backport (recency / severity / product call)."
            )
        elif lbl == "FP":
            notes.append(
                f"    - {b}: FP (undetermined): pure-addition fix (nothing removed to "
                f"check), so pre-image presence can't be judged deterministically."
            )
        elif lbl == "FN":
            notes.append(
                f"    - {b}: FALSE NEGATIVE (a branch the humans backported that the "
                f"tool would skip). This is the dangerous direction."
            )
        ai = v.get("ai")
        if ai is not None:
            likely = {True: "affected", False: "not affected", None: "uncertain"}[
                ai.get("likely_affected")
            ]
            tag = (
                " [OVERRODE deterministic]" if ai.get("overrode_deterministic") else ""
            )
            notes.append(
                f"    - {b}: AI {ai.get('role', '?')} says '{likely}' "
                f"({ai.get('confidence', '?')} confidence){tag}"
            )
    if notes:
        out.append("\n  Notes:")
        out.extend(notes)
    return "\n".join(out), labels


def replay_one_fix(job):
    """Replay a single fix end-to-end and return a buffered result.

    `job` is a plain dict (picklable) so this can run either in-process or inside
    a ProcessPoolExecutor worker. All human-readable output is accumulated into a
    string and returned rather than printed, so the caller can emit each fix's
    report atomically and in submission order even when fixes run concurrently.

    Returns a dict: {"text": str, "labels": [(lbl, preimage), ...], "counted": bool}
    where `counted` is False for a fix that was skipped (unresolved / no diff) and
    therefore should not count toward the "fixes replayed" tally.
    """
    repo = job["repo"]
    ref = job["ref"]
    label = job["label"]
    branches = job["branches"]

    # In a spawned worker, re-assert the deterministic-only env so a stale/absent
    # Bedrock token can't add noise or latency on a --no-ai run.
    if not job["with_ai"]:
        os.environ["BACKPORT_DISABLE_AI"] = "1"

    out = []

    fix_sha = resolve_ref(repo, ref)
    if fix_sha is None:
        out.append(
            f"\n[skip] {ref}: could not resolve to a mainline commit "
            f"(unknown SHA/ref, or no PR #{ref} found on origin/main)"
        )
        return {"text": "\n".join(out), "labels": [], "counted": False}
    if str(ref).lstrip("#").strip() != fix_sha:
        out.append(f"\nresolved {ref} -> {fix_sha[:12]}")
    if label is None:
        label = subject(repo, fix_sha)
    if not get_changed_files_safe(repo, fix_sha):
        out.append(f"\n[skip] {ref}: no diff (merge commit?)")
        return {"text": "\n".join(out), "labels": [], "counted": False}

    gt = discover_ground_truth(repo, fix_sha, branches, label=label)
    if job["truth"] is not None:
        wanted = {b.strip() for b in job["truth"].split(",") if b.strip()}
        for b in branches:
            gt[b]["affected"] = b in wanted
            gt[b]["via"] = "manual" if b in wanted else gt[b]["via"]

    # Support-window filter: drop branches that were out of support as of this
    # fix's date, so the tool isn't scored for "skipping" an EOL branch.
    as_of = commit_date(repo, fix_sha)
    scoped, dropped = filter_by_support_window(job["manifest"], branches, as_of)
    if dropped:
        out.append(
            f"\n  out of support as of {as_of} (excluded): "
            + ", ".join(f"{b} ({why})" for b, why in dropped)
        )

    # Forked-AFTER-the-fix branches: a branch cut from main AFTER this fix landed
    # has the fix as a direct ancestor -- it was born already containing the fix
    # (no backport was ever made or needed). We DO NOT drop these; we keep them in
    # the table so the full picture is visible, clearly labelled as such. They are
    # not real backport candidates (they didn't exist when the fix landed), so the
    # correct bot action is simply to skip them.
    forked_after = set(
        b
        for b in scoped
        if subprocess.run(
            ["git", "-C", repo, "merge-base", "--is-ancestor", fix_sha, f"origin/{b}"]
        ).returncode
        == 0
    )

    sandbox, rollbacks = build_sandbox(repo, fix_sha, gt, scoped)
    try:
        files, introducers, verdicts = run_engine(
            sandbox, fix_sha, scoped, job["cherry_pick"], jobs=job["jobs"]
        )
        text, labels = format_scenario(
            repo,
            fix_sha,
            label,
            files,
            introducers,
            gt,
            rollbacks,
            verdicts,
            scoped,
            sla_days=job.get("sla_days", 0),
            forked_after=forked_after,
        )
        out.append(text)
    finally:
        if job["keep"]:
            out.append(f"  (KEEP_SANDBOX=1 -> sandbox left at {sandbox})")
        else:
            shutil.rmtree(sandbox, ignore_errors=True)

    return {"text": "\n".join(out), "labels": labels, "counted": True}


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[1])
    ap.add_argument("commits", nargs="*", help="fix commits/refs on mainline to replay")
    ap.add_argument("--repo", default=DEFAULT_REPO, help="path to the aws-lc clone")
    ap.add_argument(
        "--file",
        "-f",
        default=None,
        help="path to a list of fix commits/PR-numbers to replay, one per line "
        "(blank lines and '//' or '# text' comments ignored; '#1917' is a PR number)",
    )
    ap.add_argument("--branches", nargs="+", default=DEFAULT_BRANCHES)
    ap.add_argument(
        "--cherry-pick",
        action="store_true",
        help="also attempt the cherry-pick apply (slower: checks out each branch)",
    )
    ap.add_argument(
        "--no-ai",
        action="store_true",
        help="disable the AI advisory layer and run the deterministic engine ONLY. "
        "AI is ON by default; use this only for offline/no-creds deterministic checks.",
    )
    ap.add_argument(
        "--sla-days",
        type=int,
        default=90,
        help="backport SLA window in days (default 90). An affected branch that a "
        "fix younger than this hasn't been backported to yet is counted as "
        "'pending (too recent)', not a false positive — the branch IS affected, "
        "the team just hasn't shipped it yet. Set 0 to disable (score strictly).",
    )
    ap.add_argument(
        "--truth",
        default=None,
        help="override discovered ground truth (comma-separated affected branches); "
        "only valid with a single commit",
    )
    ap.add_argument(
        "--answers",
        default=None,
        help="per-fix hand-verified answer key: each line '<ref> br1,br2,...' lists "
        "the AFFECTED branches (the ones the bot should flag after rollback). "
        "Overrides auto ground-truth for scoring AND rollback.",
    )
    ap.add_argument(
        "--versions",
        default=DEFAULT_VERSIONS,
        help="support-window manifest (fips_versions.json shape); branches past "
        "end-of-support as of a fix's date are dropped from that fix's analysis",
    )
    ap.add_argument(
        "--no-version-filter",
        action="store_true",
        help="disable the support-window filter (analyze every requested branch)",
    )
    ap.add_argument(
        "--jobs",
        "-j",
        type=int,
        default=6,
        help="branches to analyze concurrently (default 6; use 1 to disable). "
        "The big speedup when AI is on, since each branch is its own Bedrock call.",
    )
    ap.add_argument(
        "--fix-jobs",
        "-J",
        type=int,
        default=0,
        help="fixes to replay concurrently, each in its own process (default: auto). "
        "Auto picks a sweet spot from your CPU count (deterministic sweeps) or a "
        "throttle-safe concurrent-Bedrock budget when AI is on). Pass an explicit N to "
        "override, or 1 to disable. Output stays in list order regardless.",
    )
    args = ap.parse_args()

    repo = str(Path(args.repo).expanduser().resolve())
    if not Path(repo, ".git").exists():
        print(f"[error] {repo} is not a git repo", file=sys.stderr)
        return 2
    if rev_parse(repo, "origin/main") is None:
        print(f"[error] {repo} has no origin/main", file=sys.stderr)
        return 2

    # AI is ON by default: this harness should mirror how the bot actually runs.
    # Only --no-ai forces the deterministic-only path (offline / no-creds checks).
    with_ai = not args.no_ai
    if with_ai:
        # Make sure a stale env var can't silently disable AI behind our back.
        os.environ.pop("BACKPORT_DISABLE_AI", None)
    else:
        os.environ["BACKPORT_DISABLE_AI"] = "1"

    examples = [(tok, None) for tok in args.commits]
    if args.file:
        examples += read_commits_file(args.file)
    if not examples:
        examples = list(BUILTIN_EXAMPLES)
    if args.truth and len(examples) != 1:
        print("[error] --truth requires exactly one commit", file=sys.stderr)
        return 2

    print("Read-only replay against", repo)
    print("(no pushes, no gh, no mutation of the real repo; throwaway sandbox only)")
    if with_ai:
        # We never want to *think* AI ran when it silently didn't. If the SDK or
        # credentials aren't available, ai_client() returns None and the engine
        # falls back to deterministic-only — so say so, loudly, up front.
        if ai_client() is None:
            print(
                "\n[WARN] AI is ON but the Bedrock client could not initialize "
                "(missing anthropic SDK or AWS creds). This run would fall back to "
                "DETERMINISTIC-ONLY.\n        Fix creds (e.g. `mwinit -o`; "
                "export AWS_PROFILE=... AWS_REGION=...) or pass --no-ai to "
                "acknowledge a deterministic-only run.",
                file=sys.stderr,
            )
        else:
            print("AI advisory layer: ON (auditor + tie-breaker)")
    else:
        print("AI advisory layer: OFF (--no-ai; deterministic engine only)")

    manifest = None if args.no_version_filter else load_versions(args.versions)
    if manifest:
        print(f"support-window filter: {args.versions}")
    elif not args.no_version_filter:
        print(f"[warn] no support-window manifest at {args.versions}; not filtering")

    keep = os.environ.get("KEEP_SANDBOX") == "1"

    # Optional per-fix hand-verified answer key: {ref: "br1,br2,..."}. When present,
    # a fix's affected set comes from here (not auto-discovery), for both rollback
    # and scoring. Keyed by the ref string as it appears in the input list.
    answers = {}
    if args.answers:
        for raw in open(args.answers):
            line = raw.split("#")[0].rstrip("\n").strip()
            if not line:
                continue
            parts = line.split(None, 1)
            answers[parts[0]] = parts[1].strip() if len(parts) > 1 else ""
        print(f"answer key: {args.answers} ({len(answers)} fixes)")

    def truth_for(ref):
        if answers:
            # match by the raw ref or its resolved short/long sha
            if ref in answers:
                return answers[ref]
            rp = subprocess.run(
                ["git", "-C", repo, "rev-parse", "--short=12", ref],
                capture_output=True,
                text=True,
            ).stdout.strip()
            if rp in answers:
                return answers[rp]
        return args.truth

    # Build one picklable job per requested fix, preserving list order.
    jobs = [
        {
            "repo": repo,
            "ref": ref,
            "label": label,
            "branches": args.branches,
            "cherry_pick": args.cherry_pick,
            "with_ai": with_ai,
            "truth": truth_for(ref),
            "manifest": manifest,
            "keep": keep,
            "jobs": args.jobs,
            "sla_days": args.sla_days,
        }
        for ref, label in examples
    ]

    all_labels = []
    fixes_counted = 0
    fix_jobs = args.fix_jobs
    if fix_jobs <= 0:  # auto: pick a sweet spot
        n = len(jobs)
        cpu = os.cpu_count() or 4
        if with_ai:
            # AI runs are Bedrock-latency-bound and throttle-sensitive, not
            # CPU-bound: the number of in-flight requests is fix_jobs x --jobs.
            # Cap that product to a modest budget so we don't get 429s.
            budget = 12
            fix_jobs = max(1, min(n, budget // max(1, args.jobs)))
            why = f"AI throttle budget ~{budget} concurrent Bedrock calls"
        else:
            # Deterministic sweeps are git/IO-bound; throughput plateaus around
            # half the cores (measured), and extra branch threads just
            # oversubscribe, so scale fix-level parallelism with the CPU count.
            fix_jobs = max(1, min(n, cpu // 2 if cpu > 2 else 1))
            why = f"{cpu} cores"
        if n > 1:
            print(f"[auto] --fix-jobs {fix_jobs} ({why}; override with --fix-jobs N)")
    fix_jobs = max(1, fix_jobs)
    if fix_jobs == 1 or len(jobs) <= 1:
        for job in jobs:
            res = replay_one_fix(job)
            print(res["text"])
            all_labels.extend(res["labels"])
            fixes_counted += 1 if res["counted"] else 0
    else:
        # Process pool: each fix runs in its own process with its own CWD, so the
        # engine's process-global chdir never races. Results are collected in
        # submission order so the report reads the same as a sequential run.
        with ProcessPoolExecutor(max_workers=min(fix_jobs, len(jobs))) as ex:
            for res in ex.map(replay_one_fix, jobs):
                print(res["text"])
                all_labels.extend(res["labels"])
                fixes_counted += 1 if res["counted"] else 0

    # ----- Scorecard -----
    summary = {"TP": 0, "TN": 0, "FP": 0, "FN": 0}
    # Break false positives down by whether the vulnerable code is actually on
    # the branch: a true over-flag (provably absent) is a tool error; "affected
    # but not shipped" means the code is there and the team chose not to (or
    # hasn't yet) backported — not an analysis error. Over-flags are further split
    # by WHO made the call: the deterministic engine, or an AI tie-breaker upgrade
    # (pre-image absent but the AI judged the older code still vulnerable). Only
    # the deterministic ones are true engine errors; AI upgrades are the AI's call
    # to verify separately.
    fp_not_shipped = fp_unknown = 0
    fp_overflag_det = fp_overflag_ai = 0
    fp_reimpl = 0
    fp_pending = 0  # affected, but the fix is too recent to expect a backport yet
    for lbl, preimage, ai_upgraded, reimpl, recent in all_labels:
        summary[lbl] += 1
        if lbl == "FP":
            if reimpl:
                # fix is present as a reimplementation (CVE-id match); the bot
                # can't detect it, so it over-flags a redundant PR. Not a tool
                # analysis error and not "unshipped" — the branch IS protected.
                fp_reimpl += 1
            elif preimage is False:
                if ai_upgraded:
                    fp_overflag_ai += 1
                else:
                    fp_overflag_det += 1
            elif preimage is True and recent:
                # affected AND the fix is inside the backport SLA window: the
                # team simply hasn't shipped it yet. The bot's flag is correct;
                # reclassify out of FP into 'pending' so recency isn't scored as
                # an error.
                fp_pending += 1
                summary["FP"] -= 1
            elif preimage is True:
                fp_not_shipped += 1
            else:
                fp_unknown += 1
    fp_overflag = fp_overflag_det + fp_overflag_ai
    # total counts every cell; pending cells were moved out of summary["FP"] so
    # add them back in for the denominator.
    total = summary["TP"] + summary["TN"] + summary["FN"] + summary["FP"] + fp_pending
    # 'pending' cells are correct calls (the branch is affected), so count them
    # with the agreements rather than against them.
    correct = summary["TP"] + summary["TN"] + fp_pending

    print(f"\n{'=' * 104}")
    print("Scorecard - tool verdict vs. what the team actually backported")
    print(f"{'=' * 104}")
    print(f"  fixes replayed:            {fixes_counted}")
    print(f"  (branch x fix) cells:      {total}")
    print(f"  true positives  (correctly flagged for backport): {summary['TP']}")
    print(f"  true negatives  (correctly skipped):               {summary['TN']}")
    print(f"  false positives (would open an unneeded PR):       {summary['FP']}")
    if fp_pending:
        print(
            f"  pending (affected; fix too recent to expect a backport): {fp_pending}"
        )
    if summary["FP"]:
        print(
            f"      - true over-flags (vulnerable code provably ABSENT): {fp_overflag}"
        )
        print(
            f"          . from the deterministic engine (real tool errors): {fp_overflag_det}"
        )
        print(
            f"          . from an AI tie-breaker upgrade (verify AI, not a det error): {fp_overflag_ai}"
        )
        print(
            f"      - redundant over-flags (fix present as a reimplementation): {fp_reimpl}"
        )
        print(
            f"      - affected but not (yet) backported by hand:         {fp_not_shipped}"
        )
        print(
            f"      - pure-addition / undetermined:                      {fp_unknown}"
        )
    print(f"  false negatives (MISSED a real backport):          {summary['FN']}")
    if total:
        print(f"  agreement: {correct}/{total} ({correct / total * 100:.0f}%)")
        det_fp_rate = fp_overflag_det / total * 100
        print(
            f"  DETERMINISTIC over-flag rate (real engine errors / cells): "
            f"{fp_overflag_det}/{total} ({det_fp_rate:.1f}%)"
        )
    print()
    if summary["FN"] == 0:
        print("RESULT: no false negatives (no real backport would have been missed).")
    else:
        print("RESULT: FALSE NEGATIVES present - review the flagged branches above.")
    return 0


def get_changed_files_safe(repo, sha):
    """Cheap check that the commit has a diff, run in the real repo."""
    with chdir(repo):
        try:
            return bool(get_changed_files(sha))
        except Exception:
            return False


if __name__ == "__main__":
    sys.exit(main())
