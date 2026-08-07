#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
"""
Replays real AWS-LC fixes and grades analyze against a hand-checked answer key

Each fix is replayed in a throwaway sandbox rolled back to just before it landed,
so the tool sees the world as it was and cannot spot its own backport

Run from util/backport:
    python3 testing/replay_fixes.py
    python3 testing/replay_fixes.py --no-ai --fix 9545d9de6059
"""

import argparse
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from engine.classify_branches import classify_branch
from engine.consult_ai import refine_with_ai
from engine.discover_branches import get_supported_branches
from engine.inspect_fix import (
    buggy_lines_still_present,
    deleted_lines,
    find_bug_commits,
    only_source_files,
)
from util.config import AFFECTED, ALREADY, UNSURE, fingerprint_pathspec
from util.git import changed_files_with_status, using_repo

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent.parent  # util/backport/testing -> the checkout


# _________ Reading The Bench Files _________


def read_fixes(path: Path):
    """Each line is a commit SHA then a free text label"""
    fixes = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            sha, _, label = line.partition(" ")
            fixes.append((sha, label.strip()))
    return fixes


def read_answers(path: Path):
    """Each line is a SHA then the branches that should be flagged, comma separated"""
    answers = {}
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        answers[parts[0]] = set(parts[1].split(",")) if len(parts) > 1 else set()
    return answers


# _________ Talking To The Real Checkout _________


def git_out(repo, *args) -> str:
    """Runs git in a given directory and hands back stdout, empty on failure"""
    result = subprocess.run(
        ["git", *args], cwd=str(repo), capture_output=True, text=True, check=False
    )
    return result.stdout.strip() if result.returncode == 0 else ""


def commit_time(repo, ref) -> int:
    """When a commit was made, or 0 when the ref is unknown"""
    out = git_out(repo, "show", "-s", "--format=%ct", ref)
    return int(out) if out.isdigit() else 0


def branches_in_scope(repo, fix_sha, branches):
    """
    Branches that already existed when the fix landed
    A branch cut later already carries the fix, so grading it proves nothing
    """
    when = commit_time(repo, fix_sha)
    in_scope = []
    for branch in branches:
        base = git_out(repo, "merge-base", "origin/main", f"origin/{branch}")
        if base and commit_time(repo, base) < when:
            in_scope.append(branch)
    return in_scope


def patch_ids(repo, rev_range):
    """{fingerprint: commit} for a range, generated files left out"""
    log = subprocess.run(
        ["git", "log", "-p", "--no-merges", "--format=%H", rev_range]
        + fingerprint_pathspec(),
        cwd=str(repo),
        capture_output=True,
        check=False,
    )
    if log.returncode != 0:
        return {}
    pid = subprocess.run(
        ["git", "patch-id", "--stable"],
        input=log.stdout,
        cwd=str(repo),
        capture_output=True,
        check=False,
    )
    out = pid.stdout.decode("ascii", errors="replace")
    return {
        p[0]: p[1] for p in (line.split() for line in out.splitlines()) if len(p) >= 2
    }


def find_backport(repo, fix_sha, branch):
    """
    The commit on the branch that backported this fix, so we know where to roll back
    Looks for a cherry pick trailer naming the fix, then a matching fingerprint,
    then the same subject line
    """
    rng = f"origin/main..origin/{branch}"
    short = fix_sha[:12]

    log = git_out(repo, "log", rng, "--format=%H%x1f%B%x1e")
    for entry in log.split("\x1e"):
        if "\x1f" not in entry:
            continue
        sha, body = entry.split("\x1f", 1)
        if "cherry picked from commit" in body and (short in body or fix_sha in body):
            return sha.strip(), "trailer"

    fix_pid = next(iter(patch_ids(repo, f"{fix_sha}^..{fix_sha}")), None)
    if fix_pid:
        on_branch = patch_ids(repo, rng)
        if fix_pid in on_branch:
            return on_branch[fix_pid], "fingerprint"

    subject = git_out(repo, "log", "-1", "--format=%s", fix_sha)
    trimmed = subject.split("(#")[0].strip().lower()
    if len(trimmed) > 20:
        for line in git_out(repo, "log", rng, "--format=%H%x1f%s").splitlines():
            if "\x1f" not in line:
                continue
            sha, subj = line.split("\x1f", 1)
            if trimmed in subj.strip().lower():
                return sha.strip(), "subject"
    return None, ""


# _________ The Sandbox _________


def build_sandbox(repo, fix_sha, branches, affected, backports):
    """
    A throwaway repo whose refs look like the world just before the fix landed
    origin/main becomes the fix itself, and every branch that was given the fix by
    hand is rolled back to just before that backport
    Objects are borrowed from the real checkout, so nothing is copied
    """
    sandbox = tempfile.mkdtemp(prefix="backport-replay-")
    subprocess.run(
        ["git", "init", "-q", "-b", "main", sandbox], capture_output=True, check=True
    )
    alternates = Path(sandbox, ".git", "objects", "info", "alternates")
    alternates.write_text(str(Path(repo, ".git", "objects").resolve()) + "\n")
    subprocess.run(
        ["git", "update-ref", "refs/remotes/origin/main", fix_sha],
        cwd=sandbox,
        capture_output=True,
        check=False,
    )

    for branch in branches:
        target = git_out(repo, "rev-parse", f"origin/{branch}")
        # Only branches that were given the fix by hand need winding back. A branch
        # that never got it is already in its pre-fix state
        backport = backports.get(branch) if branch in affected else None
        if backport:
            target = git_out(repo, "rev-parse", f"{backport}^") or target
        if target:
            subprocess.run(
                ["git", "update-ref", f"refs/remotes/origin/{branch}", target],
                cwd=sandbox,
                capture_output=True,
                check=False,
            )
    return sandbox


# _________ Running And Grading _________


def score(flagged: bool, truth: bool) -> str:
    """TP means correctly flagged, FN means a backport was missed"""
    if flagged:
        return "TP" if truth else "FP"
    return "FN" if truth else "TN"


def replay_one(repo, fix_sha, label, truth, jobs):
    """Replays one fix and returns a per-branch scorecard"""
    all_branches = get_supported_branches()
    branches = branches_in_scope(repo, fix_sha, all_branches)
    if not branches:
        return None

    backports = {}
    for branch in truth & set(branches):
        sha, how = find_backport(repo, fix_sha, branch)
        if sha:
            backports[branch] = (sha, how)

    sandbox = build_sandbox(
        repo, fix_sha, branches, truth, {b: v[0] for b, v in backports.items()}
    )
    # Both caches key on the branch ref, whose contents differ per sandbox, so a
    # stale entry from the previous fix would be silently wrong
    deleted_lines.cache_clear()
    buggy_lines_still_present.cache_clear()
    try:
        with using_repo(sandbox):
            files, traceable = changed_files_with_status(fix_sha)
            bug_commits = sorted(find_bug_commits(fix_sha, traceable))
            src = only_source_files(files)
            with ThreadPoolExecutor(max_workers=max(1, min(jobs, len(branches)))) as ex:
                verdicts = dict(
                    zip(
                        branches,
                        ex.map(
                            lambda b: classify_branch(fix_sha, src, bug_commits, b),
                            branches,
                        ),
                    )
                )
            # Kept so the report can say what the AI changed, and whether the
            # deleted lines are actually on the branch
            before_ai = dict(verdicts)
            still_there = {
                b: buggy_lines_still_present(fix_sha, tuple(src), f"origin/{b}")
                for b in branches
            }
            # Always go through refine_with_ai, never score classify_branch alone.
            # It turns UNSURE into AFFECTED, so a raw UNSURE is a flagged branch, not
            # a cleared one, and scoring it as cleared invents false negatives
            verdicts, decided_by = refine_with_ai(fix_sha, src, bug_commits, verdicts)
    finally:
        shutil.rmtree(sandbox, ignore_errors=True)

    rows = []
    for branch in branches:
        state = verdicts[branch]
        rows.append(
            {
                "branch": branch,
                "state": state,
                "before_ai": before_ai[branch],
                "still_there": still_there[branch],
                "why": decided_by.get(branch, ""),
                "truth": branch in truth,
                "backport": backports.get(branch, (None, ""))[1],
                "score": score(state == AFFECTED, branch in truth),
                # Should have been flagged but the fix is already here, so the
                # rollback missed a backport and this cell is not a fair test
                "stale": branch in truth and state == ALREADY,
            }
        )
    return {
        "fix": fix_sha,
        "label": label,
        "files": files,
        "bug_commits": bug_commits,
        "rows": rows,
    }


# Why a branch was flagged when the answer key says it should not have been. Only
# OVER-FLAG is a tool error; the others are the tool being right for a reason the
# answer key does not capture
OVER_FLAG = "OVER-FLAG"
UNSHIPPED = "unshipped"
UNCLEAR = "unclear"
AI_UPGRADED = "ai-upgraded"
ADDITION = "addition-only"

FLAG_NOTES = {
    OVER_FLAG: "history positively flagged this branch, yet the deleted lines are "
    "not here, so this is most likely a real tool error",
    UNSHIPPED: "the vulnerable lines really are here, the fix was just never "
    "shipped to this branch, so the flag is correct",
    UNCLEAR: "history could not tell either way, so it defaulted to affected. "
    "This is the kind the AI is meant to settle",
    AI_UPGRADED: "history was unclear and the AI called it affected, so check the "
    "AI's reasoning rather than the git logic",
    ADDITION: "the fix only adds lines, so there is nothing deleted to look for "
    "and presence cannot be judged from history",
}


def flag_reason(row):
    """Splits an unneeded flag into a real tool error or one of the excusable kinds"""
    if row["still_there"] is True:
        return UNSHIPPED
    if row["still_there"] is None:
        return ADDITION
    if row["before_ai"] == UNSURE:
        # Never a git logic error: history said it could not tell
        return AI_UPGRADED if "AI: likely affected" in row["why"] else UNCLEAR
    return OVER_FLAG


def truth_label(row):
    """How the answer key's call was backed up, for the answer key column"""
    if not row["truth"]:
        return "not affected"
    return f"affected/{row['backport']}" if row["backport"] else "affected/code"


def print_fix(result, subject):
    """A block per fix: the header, a row per branch, then notes on anything wrong"""
    print("\n" + "=" * 113)
    print(f"{result['label']}")
    print(f'  fix {result["fix"][:12]}  "{subject[:88]}"')
    print("=" * 113)
    print(f"  changed files: {result['files']}")
    print(f"  bug commits:   {[s[:10] for s in result['bug_commits']] or '(none)'}")
    print()
    print(
        f"  {'branch':<24} {'verdict':<15} {'basis':<40} " f"{'answer key':<16} result"
    )
    print(f"  {'-' * 24} {'-' * 15} {'-' * 40} {'-' * 16} {'-' * 12}")

    notes = []
    for row in result["rows"]:
        result_col = row["score"]
        if row["score"] == "FP":
            result_col = flag_reason(row)
        elif row["score"] == "FN":
            result_col = "MISSED <-"
        elif row["score"] in ("TP", "TN"):
            result_col = "OK"
        print(
            f"  {row['branch']:<24} {row['state']:<15} {row['why'][:40]:<40} "
            f"{truth_label(row):<16} {result_col}"
        )
        if row["score"] == "FP":
            notes.append(f"    - {row['branch']}: {FLAG_NOTES[flag_reason(row)]}")
        elif row["score"] == "FN":
            notes.append(
                f"    - {row['branch']}: MISSED BACKPORT, the answer key says this "
                "branch needs the fix and the tool would skip it. This is the "
                "dangerous direction"
            )
        if row["stale"]:
            notes.append(
                f"    - {row['branch']}: the fix was still present after the "
                "rollback, so this cell is not a fair test"
            )
    if notes:
        print("\n  Notes:")
        for note in notes:
            print(note)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="Replay real fixes and grade the analyze verdicts"
    )
    parser.add_argument("--fixes", default=str(HERE / "fixes.txt"))
    parser.add_argument("--answers", default=str(HERE / "answer_key.txt"))
    parser.add_argument("--fix", help="replay only this SHA")
    parser.add_argument("--no-ai", action="store_true", help="git history only")
    parser.add_argument("--jobs", type=int, default=6, help="branches at a time")
    args = parser.parse_args(argv)

    if args.no_ai:
        import os

        os.environ["BACKPORT_DISABLE_AI"] = "1"

    fixes = read_fixes(Path(args.fixes))
    answers = read_answers(Path(args.answers))
    missing = [sha for sha, _ in fixes if sha not in answers]
    if missing:
        print(f"error: no answer key entry for {', '.join(missing)}", file=sys.stderr)
        return 1
    if args.fix:
        fixes = [(s, l) for s, l in fixes if s.startswith(args.fix)]
        if not fixes:
            print(f"error: {args.fix} is not in the bench", file=sys.stderr)
            return 1

    totals = {"TP": 0, "TN": 0, "FP": 0, "FN": 0}
    flag_kinds = {OVER_FLAG: 0, UNSHIPPED: 0, UNCLEAR: 0, AI_UPGRADED: 0, ADDITION: 0}
    stale = []
    print(f"Replaying {len(fixes)} fix(es), AI {'off' if args.no_ai else 'on'}\n")
    for sha, label in fixes:
        result = replay_one(REPO, sha, label, answers[sha], args.jobs)
        if result is None:
            print(f"{sha[:12]}  skipped, no branch predates this fix")
            continue
        print_fix(result, git_out(REPO, "log", "-1", "--format=%s", sha))
        for row in result["rows"]:
            totals[row["score"]] += 1
            if row["score"] == "FP":
                flag_kinds[flag_reason(row)] += 1
            if row["stale"]:
                stale.append((sha[:12], row["branch"]))

    cells = sum(totals.values())
    print(f"\n{'=' * 113}")
    print(f"{cells} branch cells over {len(fixes)} fix(es)")
    print(f"{'=' * 113}")
    print(f"  correctly flagged     {totals['TP']}")
    print(f"  correctly cleared     {totals['TN']}")
    print(f"  unneeded flags        {totals['FP']}")
    print(
        f"      real over-flags   {flag_kinds[OVER_FLAG]}  "
        "history flagged it but the lines are absent, a tool error"
    )
    print(
        f"      never shipped     {flag_kinds[UNSHIPPED]}  "
        "lines still there, the flag is correct"
    )
    print(
        f"      unclear           {flag_kinds[UNCLEAR]}  "
        "history could not tell, defaulted to affected"
    )
    print(
        f"      AI upgraded       {flag_kinds[AI_UPGRADED]}  "
        "history unclear, the AI called it affected"
    )
    print(
        f"      addition only     {flag_kinds[ADDITION]}  "
        "nothing deleted to look for"
    )
    print(f"  MISSED BACKPORTS      {totals['FN']}")
    if cells:
        print(
            f"  agreement             "
            f"{100 * (totals['TP'] + totals['TN']) // cells}%"
        )
    if stale:
        print(f"\n{len(stale)} cell(s) still had the fix, rollback missed a backport:")
        for sha, branch in stale:
            print(f"  {sha} {branch}")
    return 1 if totals["FN"] else 0


if __name__ == "__main__":
    sys.exit(main())
