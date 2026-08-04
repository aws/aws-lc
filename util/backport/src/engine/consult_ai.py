"""
The AI layer, asked only about branches git history cannot settle
Advisory: it can add flags for a human to review but never hide a backport
"""

from engine.inspect_fix import (
    bug_commits_present,
    buggy_lines_still_present,
    deleted_lines,
    is_comment_or_blank,
    normalize_spaces,
)
from engine.prompts import (
    ALL_ABSENT_NOTE,
    AUDITOR_TASK,
    BUGGY_LINES_GONE_NOTE,
    SOME_ABSENT_NOTE,
    SYSTEM_PROMPT,
    TIEBREAKER_TASK,
)
from util.config import (
    AFFECTED,
    MAX_FILE_BYTES,
    NOT_AFFECTED,
    UNSURE,
    load_model_config,
)
from util.git import get_commit_diff, get_file_on_branch, git, git_in_repo, show_file

import os
import re
import sys
from functools import lru_cache
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

try:
    import anthropic
except ImportError:
    anthropic = None

# _________ The Bedrock Client _________


@lru_cache(maxsize=1)
def ai_client():
    """A Bedrock client, or None when the SDK or AWS credentials are missing"""
    if anthropic is None or os.environ.get("BACKPORT_DISABLE_AI") == "1":
        return None
    # Credentials come from the normal AWS chain, not just AWS_ACCESS_KEY_ID,
    # which misses anything set up in ~/.aws
    try:
        import boto3

        if boto3.Session().get_credentials() is None:
            return None
    except ImportError:
        if not os.environ.get("AWS_ACCESS_KEY_ID"):
            return None
    return anthropic.AnthropicBedrock(aws_region=load_model_config()["aws_region"])


# _________ What The Model Sees _________

# Common C tokens say nothing about what the fix touched
C_STOPWORDS = set(
    """const return void static struct union switch case default break continue
    while else goto sizeof include size_t unsigned signed openssl NULL true false
    uint8_t uint16_t uint32_t uint64_t int8_t int16_t int32_t int64_t""".split()
)
IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_]{4,}")


def key_symbols(commit: str, file: str) -> List[str]:
    """Identifiers the fix touches, whose presence on a branch is real evidence"""
    diff = git_in_repo(
        ["diff", "-U0", f"{commit}^", commit, "--", file],
        capture_output=True,
        text=True,
        errors="replace",
    )
    if diff.returncode != 0:
        return []
    found = []
    for line in diff.stdout.splitlines():
        if line.startswith("@@"):
            # The enclosing function name follows the second @@
            text = line.split("@@")[-1]
        elif line[:1] in ("+", "-") and line[:3] not in ("+++", "---"):
            if is_comment_or_blank(line[1:], file):
                continue
            text = line[1:]
        else:
            continue
        for match in IDENTIFIER.finditer(text):
            name = match.group(0)
            if name.lower() not in C_STOPWORDS and name not in found:
                found.append(name)
    return found[:10]


def region_around(
    content: str, needles: Iterable[str], window: int = 60
) -> Optional[Tuple[str, Tuple[int, int]]]:
    """
    The slice of the file around the first line matching any needle
    Lets the model see the relevant code instead of a file cut off at the top
    """
    lines = content.splitlines()
    normalized = [normalize_spaces(line) for line in lines]
    for needle in needles:
        target = normalize_spaces(needle)
        if not target:
            continue
        for i, line in enumerate(normalized):
            if target in line:
                lo = max(0, i - window)
                hi = min(len(lines), i + window)
                return "\n".join(lines[lo:hi]), (lo + 1, hi)
    return None


def symbol_presence(commit: str, changed_files: Sequence[str], branch_ref: str) -> str:
    """Which symbols the fix touches exist on the branch, as plain fact"""
    rows = []
    for file in changed_files[:6]:
        content = show_file(branch_ref, file)
        if content is None:
            continue
        for symbol in key_symbols(commit, file):
            here = re.search(rf"\b{re.escape(symbol)}\b", content) is not None
            row = f"- `{symbol}` ({file}): {'present' if here else 'ABSENT'}"
            if row not in rows:
                rows.append(row)
    if not rows:
        return ""
    return (
        "\n\n### Symbols the fix touches, and whether they exist here\n"
        "(a symbol the fix modifies that is ABSENT is strong evidence the "
        "vulnerable code path is not present):\n" + "\n".join(rows[:20])
    )


def branch_file_context(
    commit: str, branch: str, branch_ref: str, changed_files: Sequence[str]
) -> Tuple[str, List[str], bool]:
    """The fixed files as they look on the branch, plus the ones that are missing"""
    parts, absent = [], []
    for file in changed_files[:6]:  # capped to keep the prompt a sane size
        content, resolved = get_file_on_branch(file, branch_ref, commit=commit)
        if not content:
            absent.append(file)
            continue
        label = file if resolved == file else f"{resolved} (older path of {file})"
        full = show_file(branch_ref, resolved) or content
        region = region_around(full, deleted_lines(commit, file))
        if region:
            excerpt, (lo, hi) = region
            parts.append(
                f"### {label} (on {branch}, lines {lo}-{hi}, around the change)\n"
                f"```\n{excerpt[:MAX_FILE_BYTES]}\n```"
            )
        else:
            parts.append(f"### {label} (on {branch})\n```\n{content}\n```")
    if not parts:
        return "(none of the files the fix changes were found here)", absent, False
    return "\n\n".join(parts), absent, True


def absence_note(absent_files: Sequence[str], any_present: bool) -> str:
    """Says absence was verified, so the model reads it as evidence"""
    if not absent_files:
        return ""
    listing = "\n".join(f"- {f}" for f in absent_files)
    return (
        "\n\n### Files the fix changes that are NOT present here\n"
        "(checked against the current path and every older path):\n"
        + listing
        + (SOME_ABSENT_NOTE if any_present else ALL_ABSENT_NOTE)
    )


def build_prompt(
    commit: str,
    branch: str,
    branch_ref: str,
    changed_files: Sequence[str],
    bug_commits: Iterable[str],
    flagged_affected: bool,
) -> str:
    """The user message: the fix, the branch's copy of the code, and the task"""
    context, absent, any_present = branch_file_context(
        commit, branch, branch_ref, changed_files
    )
    # Only tell the auditor the lines are gone, the tie-breaker has no flag to audit
    lines_gone = (
        flagged_affected
        and buggy_lines_still_present(commit, tuple(changed_files), branch_ref) is False
    )
    return (
        f"## Impact Analysis Request\n\n"
        f"**Fix commit:** `{commit}`\n"
        f"**Target branch:** `{branch}`\n"
        f"**Commits that wrote these lines:** "
        f"{', '.join(list(bug_commits)[:5]) or '(none found)'}\n\n"
        f"### What the fix changes on main\n"
        f"```diff\n{get_commit_diff(commit)}\n```\n\n"
        f"### The same files on the target branch\n{context}"
        f"{absence_note(absent, any_present)}"
        f"{symbol_presence(commit, changed_files, branch_ref)}"
        f"{BUGGY_LINES_GONE_NOTE if lines_gone else ''}\n\n"
        f"{AUDITOR_TASK.format(branch=branch) if flagged_affected else TIEBREAKER_TASK}"
    )


# _________ Asking The Model _________


def read_answer(raw: str) -> Tuple[Optional[bool], str]:
    """Pulls (likely affected, confidence) out of the reply"""
    likely, confidence = None, "low"
    for line in raw.splitlines():
        low = line.lower()
        if "likely affected" in low:
            if "yes" in low:
                likely = True
            elif "no" in low:
                likely = False  # anything else stays None, meaning uncertain
        if "confidence" in low:
            for level in ("high", "medium", "low"):
                if level in low:
                    confidence = level
                    break
    return likely, confidence


def ask_about_branch(
    commit: str,
    branch: str,
    changed_files: Sequence[str],
    bug_commits: Iterable[str],
    flagged_affected: bool = False,
) -> Optional[Tuple[Optional[bool], str]]:
    """
    Asks whether the branch is affected, as (likely affected, confidence)
    None when the model could not be reached at all
    """
    client = ai_client()
    if client is None:
        return None
    prompt = build_prompt(
        commit, branch, f"origin/{branch}", changed_files, bug_commits, flagged_affected
    )
    cfg = load_model_config()
    try:
        with client.messages.stream(
            model=cfg["model_id"],
            max_tokens=cfg["max_tokens"],
            thinking={"type": "adaptive"},
            system=SYSTEM_PROMPT,
            messages=[{"role": "user", "content": prompt}],
        ) as stream:
            reply = stream.get_final_message()
    # Deliberately broad. Any failure here (network, auth, throttling, a model
    # error) must leave the branch flagged rather than crash the run, since the
    # AI is advisory
    except Exception as exc:
        print(f"[ai] call failed for {branch}: {exc}", file=sys.stderr)
        return None
    if reply.stop_reason == "max_tokens":
        # Thinking tokens ate the budget, so the answer may be cut off mid-sentence
        print(
            f"[ai] reply for {branch} hit the token limit and may be cut short, "
            "raise max_tokens in model-config.json",
            file=sys.stderr,
        )
    raw = "".join(b.text for b in reply.content if hasattr(b, "text"))
    return read_answer(raw.strip())


# _________ Settling The Unsure Branches _________


def decide_unsure(
    fix_sha: str,
    files: Sequence[str],
    bug_commits: Sequence[str],
    buckets: Dict[str, str],
    decided_by: Dict[str, str],
) -> Tuple[int, int]:
    """
    Turns every UNSURE branch into AFFECTED or NOT_AFFECTED
    No answer means AFFECTED, so this can over-flag but never miss a backport
    Returns (asked, failed)
    """
    asked = failed = 0
    for branch in [b for b, s in buckets.items() if s == UNSURE]:
        asked += 1
        answer = ask_about_branch(fix_sha, branch, files, bug_commits)
        if answer is None:
            failed += 1
            buckets[branch] = AFFECTED
            decided_by[branch] = "unclear, AI unreachable, flagged for review"
            continue
        likely, confidence = answer
        if likely is True:
            buckets[branch] = AFFECTED
            decided_by[branch] = f"AI: likely affected ({confidence})"
        elif likely is False:
            buckets[branch] = NOT_AFFECTED
            decided_by[branch] = f"AI: likely not affected ({confidence})"
        else:
            buckets[branch] = AFFECTED
            decided_by[branch] = f"AI: uncertain ({confidence}), flagged for review"
    return asked, failed


# _________ Reviewing Suspicious Flags _________


def commit_time(sha: str) -> int:
    """When the commit was made, or 0. Used to find the newest bug commit"""
    out = git("show", "-s", "--format=%ct", sha, check=False).stdout.strip()
    return int(out) if out.isdigit() else 0


def likely_over_flagged(
    bug_commits: Sequence[str], buckets: Dict[str, str]
) -> Dict[str, Tuple[int, int]]:
    """
    AFFECTED branches that are probably wrong, worked out without the AI
    One matching commit is enough to flag a branch, so a fix that also touched
    old shared code can match branches older than the bug itself
    The tell is having some of those commits but not the newest one
    """
    suspects: Dict[str, Tuple[int, int]] = {}
    commits = list(bug_commits)
    if len(commits) < 2:
        return suspects  # a lone match has no old-versus-new split to doubt
    newest = max(commits, key=commit_time)
    for branch, state in buckets.items():
        if state != AFFECTED:
            continue
        here = bug_commits_present(set(commits), branch)
        if here and newest not in here:
            suspects[branch] = (len(here), len(commits))
    return suspects


def note_over_flags(
    fix_sha: str,
    files: Sequence[str],
    bug_commits: Sequence[str],
    suspects: Dict[str, Tuple[int, int]],
    decided_by: Dict[str, str],
) -> Tuple[int, int]:
    """
    Adds a review note to suspicious branches, never changes the verdict
    They stay AFFECTED even when the AI disagrees, so noise can drop but a real
    backport can never be hidden
    """
    asked = failed = 0
    for branch, (here, total) in suspects.items():
        asked += 1
        answer = ask_about_branch(fix_sha, branch, files, bug_commits, True)
        if answer is None:
            failed += 1
            decided_by[branch] = f"matched {here}/{total} bug commits, newest absent"
            continue
        likely, confidence = answer
        if likely is False:
            decided_by[branch] = f"AI suspects false positive ({confidence}), confirm"
        elif likely is True:
            decided_by[branch] = f"affected, AI agrees ({confidence})"
        else:
            decided_by[branch] = f"affected, AI uncertain ({confidence}), review"
    return asked, failed


# _________ What The Command Calls _________


def warn_if_unreachable(asked: int, failed: int) -> None:
    """
    Says so when every call failed, since the run still looks normal otherwise
    Nothing is missed, but the verdicts are noisier than the tool can manage
    """
    if not asked or failed < asked:
        return
    print(
        f"\nwarning: the AI was unreachable for all {asked} branch(es) that needed "
        "it.\n         Those are flagged AFFECTED for review, so nothing is missed, "
        "but\n         expect extra flags. Check your AWS credentials and region.",
        file=sys.stderr,
    )


def refine_with_ai(
    fix_sha: str,
    files: Sequence[str],
    bug_commits: Sequence[str],
    buckets: Dict[str, str],
) -> Tuple[Dict[str, str], Dict[str, str]]:
    """Settles the unsure branches, then reviews flags that look wrong"""
    decided_by = {branch: "git history" for branch in buckets}

    unsure = sum(1 for s in buckets.values() if s == UNSURE)
    if unsure:
        print(
            f"{unsure} branch(es) unclear from history, asking AI...\n", file=sys.stderr
        )
    # Snapshot before anything moves, so the review pass below only looks at
    # branches history positively flagged, not ones just promoted from unclear
    from_history = dict(buckets)
    asked, failed = decide_unsure(fix_sha, files, bug_commits, buckets, decided_by)

    suspects = likely_over_flagged(bug_commits, from_history)
    if suspects:
        print(
            f"{len(suspects)} flagged branch(es) match only part of the fix's "
            "history, asking AI for a review note...\n",
            file=sys.stderr,
        )
        more_asked, more_failed = note_over_flags(
            fix_sha, files, bug_commits, suspects, decided_by
        )
        asked += more_asked
        failed += more_failed

    warn_if_unreachable(asked, failed)
    return buckets, decided_by
