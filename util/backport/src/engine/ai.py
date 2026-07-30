"""
The AI advisory layer.

Layer: advisory. Builds on ``util.config`` + ``util.git`` + ``engine.analysis``;
consulted by the commands, never by the deterministic engine -- so the verdict
never depends on a model being reachable.

`ai_impact_analysis` asks Claude (via Amazon Bedrock) whether a branch is
affected, in one of two roles: AUDITOR (deterministic said affected -> look for a
false positive) or TIE-BREAKER (deterministic inconclusive -> second opinion).
`refine_with_ai` is the entry point the commands call: it turns every UNSURE
branch into a definite verdict and annotates suspicious AFFECTED ones.

Output is ADVISORY ONLY: it never cherry-picks, opens PRs, or resolves conflicts,
and the gating is directional -- it can add review noise but never cause a silent
miss. If the SDK or AWS credentials are unavailable, every entry point here
degrades to `None` and the deterministic engine runs alone.
"""

import os
import re
import subprocess
import sys
from typing import Dict, Sequence, Tuple

try:
    import anthropic as _anthropic_module
except ImportError:
    _anthropic_module = None

from engine.analysis import (
    deleted_lines,
    is_comment_or_blank,
    normalize_spaces,
    bug_commits_present,
    buggy_lines_still_present,
)
from util.config import (
    AFFECTED,
    AWS_REGION,
    MAX_FILE_BYTES,
    MAX_TOKENS,
    MODEL_ID,
    NOT_AFFECTED,
    UNSURE,
)
from util.git import get_commit_diff, get_file_on_branch, git, show_file

# ---------------------------------------------------------------------------
# Bedrock client
# ---------------------------------------------------------------------------


def ai_client():
    """An AnthropicBedrock client if the SDK and AWS credentials are available,
    else None (BACKPORT_DISABLE_AI=1 also forces None)."""
    if _anthropic_module is None:
        return None
    if os.environ.get("BACKPORT_DISABLE_AI") == "1":
        return None
    region = AWS_REGION
    # Resolve creds via the standard AWS chain (env, ~/.aws, SSO, IAM role), not
    # just AWS_ACCESS_KEY_ID which misses creds in ~/.aws/credentials.
    try:
        import boto3

        if boto3.Session().get_credentials() is None:
            return None
    except ImportError:
        if not os.environ.get("AWS_ACCESS_KEY_ID"):
            return None
    return _anthropic_module.AnthropicBedrock(aws_region=region)


_C_STOPWORDS = {
    "const",
    "return",
    "void",
    "static",
    "struct",
    "union",
    "switch",
    "case",
    "default",
    "break",
    "continue",
    "while",
    "else",
    "goto",
    "sizeof",
    "include",
    "size_t",
    "uint8_t",
    "uint16_t",
    "uint32_t",
    "uint64_t",
    "int8_t",
    "int16_t",
    "int32_t",
    "int64_t",
    "unsigned",
    "signed",
    "openssl",
    "NULL",
    "true",
    "false",
}
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]{4,}")


# ---------------------------------------------------------------------------
# Prompt context builders (what the model sees about the branch)
# ---------------------------------------------------------------------------


def key_symbols(commit, file):
    """Identifiers the fix touches in *file*: enclosing-function names from hunk
    headers plus notable identifiers on changed lines, minus common C tokens.
    These are the things whose presence on a branch signals real applicability."""
    diff = subprocess.run(
        ["git", "diff", "-U0", f"{commit}^", commit, "--", file],
        capture_output=True,
        text=True,
        errors="replace",
    )
    syms, seen = [], set()

    def add(s):
        if s and s.lower() not in _C_STOPWORDS and s not in seen:
            seen.add(s)
            syms.append(s)

    if diff.returncode == 0:
        for line in diff.stdout.splitlines():
            if line.startswith("@@"):  # enclosing function context after 2nd @@
                for m in _IDENT_RE.finditer(line.split("@@")[-1]):
                    add(m.group(0))
            elif (line.startswith("+") or line.startswith("-")) and line[:3] not in (
                "+++",
                "---",
            ):
                if is_comment_or_blank(
                    line[1:], file
                ):  # don't pull identifiers from comments
                    continue
                for m in _IDENT_RE.finditer(line[1:]):
                    add(m.group(0))
    return syms[:10]


def region_around(content, needles, window=60):
    """Slice of *content* centered on the first line matching any of *needles*
    (whitespace-normalized), with +/- *window* lines of context. Returns
    (excerpt, (start_line, end_line)) or None if nothing matches — which lets the
    model see the *relevant* code instead of a head-truncated file."""
    lines = content.splitlines()
    norm = [normalize_spaces(x) for x in lines]
    for nd in needles:
        n = normalize_spaces(nd)
        if not n:
            continue
        for i, ln in enumerate(norm):
            if n in ln:
                lo = max(0, i - window)
                hi = min(len(lines), i + window)
                return "\n".join(lines[lo:hi]), (lo + 1, hi)
    return None


def symbol_presence(commit, changed_files, branch_ref):
    """Factual table of whether the symbols the fix touches exist on the branch.
    Returns a markdown snippet, or '' if nothing distinctive was found."""
    rows = []
    for f in changed_files[:6]:
        content = show_file(branch_ref, f)
        if content is None:
            continue
        for sym in key_symbols(commit, f):
            present = re.search(rf"\b{re.escape(sym)}\b", content) is not None
            rows.append(f"- `{sym}` ({f}): {'present' if present else 'ABSENT'}")
    if not rows:
        return ""
    # de-dup while preserving order
    seen, uniq = set(), []
    for r in rows:
        if r not in seen:
            seen.add(r)
            uniq.append(r)
    return (
        "\n\n### Symbols the fix touches, and whether they exist on this branch\n"
        "(a symbol the fix modifies that is ABSENT here is strong evidence the "
        "vulnerable code path isn't present):\n" + "\n".join(uniq[:20])
    )


# ---------------------------------------------------------------------------
# Advisory entry point
# ---------------------------------------------------------------------------


# --- Prompt text (kept as constants so the function body reads as logic) ------

_SYSTEM_PROMPT = (
    "You are a security-focused code review assistant integrated into an "
    "automated CVE backport pipeline for AWS-LC (Amazon's cryptographic library). "
    "Your task is to assess whether a specific release branch is affected by a "
    "vulnerability that was fixed on main.\n\n"
    "IMPORTANT CONSTRAINTS:\n"
    "- Your analysis is ADVISORY ONLY. It will be surfaced in a GitHub PR comment "
    "for human review and must never be automatically applied or acted on.\n"
    "- Do not speculate beyond what the code evidence shows.\n"
    "- If a file modified by the fix is reported as NOT present on the branch "
    "(verified across rename history), treat that as positive evidence the branch "
    "predates the code and is not affected — not as missing information.\n"
    "- If the diff or file contents are truncated or genuinely unclear, say so and "
    "lower your confidence accordingly.\n"
    "- Output must be plain Markdown suitable for a GitHub comment."
)

_AUDITOR_TASK = (
    "---\n"
    "The deterministic engine flagged `{branch}` as AFFECTED: the "
    "bug commit(s) for the patched lines are in its history (or "
    "match by fingerprint). That heuristic takes the OLDEST commit to touch "
    "those lines, which OVER-FLAGS when the lines originate from "
    "vendored/imported third-party code (e.g. a bulk BoringSSL import) "
    "that predates every release branch and was never actually vulnerable "
    "here. Your job is to AUDIT for that false positive.\n\n"
    "1. Is the vulnerable code shown in the diff genuinely present and "
    "reachable on this branch, or is the ancestry match coming from "
    "imported/boilerplate code that was never exploitable here?\n"
    "2. Is the fix behaviourally meaningful? If the change is purely "
    "cosmetic — a variable/identifier rename, reformatting, or comment-only "
    "edit with no change in logic — it neither introduces nor removes a "
    "vulnerability, so this file is not by itself a reason to backport; say "
    "so if that is the case.\n"
    "3. Is there concrete evidence this branch is NOT actually impacted "
    "despite the ancestry match? Absent strong evidence, assume the "
    "deterministic flag is correct.\n"
    "4. What is your confidence level (high/medium/low) and why?\n\n"
    "Respond with:\n"
    "- **Likely affected**: Yes / No / Uncertain\n"
    "- **Confidence**: high / medium / low\n"
    "- **Reasoning**: 2-4 sentences\n"
    "- **Recommendation**: brief action for the human reviewer (note that "
    "the backport PR is opened regardless; a 'No' here is a caveat for "
    "the reviewer, not a cancellation)"
)

_TIEBREAKER_TASK = (
    "---\n"
    "Deterministic ancestry checks (SHA ancestry and fingerprint matching) were "
    "inconclusive for this branch. Please assess:\n\n"
    "1. Does the branch likely contain the vulnerable code shown in the diff?\n"
    "2. If so, does the fix apply cleanly in spirit (even if a cherry-pick "
    "conflicts due to diverged context)?\n"
    "3. What is your confidence level (high/medium/low) and why?\n\n"
    "Respond with:\n"
    "- **Likely affected**: Yes / No / Uncertain\n"
    "- **Confidence**: high / medium / low\n"
    "- **Reasoning**: 2-4 sentences\n"
    "- **Recommendation**: brief action for the human reviewer"
)

_ALL_ABSENT_NOTE = (
    "\n\nNone of the fixed files exist on this branch under any name. "
    "That almost always means the vulnerable code was introduced AFTER "
    "this branch diverged, so the branch is NOT affected. Only withhold "
    "that conclusion if you have concrete evidence the same logic was "
    "copied into a differently-named file on this branch."
)

_SOME_ABSENT_NOTE = (
    "\n\nThese specific files are absent (likely added after this branch "
    "diverged); base your assessment on the files that ARE shown above."
)

_PREIMAGE_ABSENT_NOTE = (
    "\n\n### Deterministic signal: the deleted lines are ABSENT here\n"
    "The exact code lines this fix changes or removes are NOT present on this "
    "branch (matched ignoring whitespace and comments). That is strong "
    "evidence the vulnerable code path does not exist on this branch. Treat "
    "this branch as NOT affected unless you can point to the same logic "
    "present in a materially different (e.g. renamed or refactored) form."
)

_ADVISORY_WRAP = (
    "<details>\n"
    "<summary>🤖 AI Impact Analysis (advisory — not auto-applied)</summary>\n\n"
    "{raw}\n\n"
    "</details>"
)


def branch_file_context(commit, branch, branch_ref, changed_files):
    """Snapshots of the fixed files as they exist on the branch (excerpted around
    the change), plus the list of files that are absent under any name. Returns
    (file_context_markdown, absent_files, any_present)."""
    parts, absent = [], []
    for f in changed_files[:6]:  # cap file count to control prompt size
        content, resolved = get_file_on_branch(f, branch_ref, commit=commit)
        if not content:
            absent.append(f)
            continue
        label = f if resolved == f else f"{resolved} (pre-rename path of {f})"
        # Center the excerpt on the changed code rather than head-truncating.
        full = show_file(branch_ref, resolved) or content
        region = region_around(full, deleted_lines(commit, f))
        if region:
            excerpt, (lo, hi) = region
            parts.append(
                f"### {label} (on {branch}, lines {lo}-{hi}, around the change)\n"
                f"```\n{excerpt[:MAX_FILE_BYTES]}\n```"
            )
        else:
            parts.append(f"### {label} (on {branch})\n```\n{content}\n```")
    context = (
        "\n\n".join(parts)
        if parts
        else "(none of the files modified by the fix were found on this branch)"
    )
    return context, absent, bool(parts)


def absence_note(absent_files, any_present):
    """Explicit 'verified not present' signal for the files absent on the branch,
    so the model reads absence as evidence, not missing information."""
    if not absent_files:
        return ""
    note = (
        "\n\n### Files modified by the fix that are NOT present on this branch\n"
        "(verified against the current path AND every prior path via rename "
        "history):\n" + "\n".join(f"- {f}" for f in absent_files)
    )
    return note + (_SOME_ABSENT_NOTE if any_present else _ALL_ABSENT_NOTE)


def buggy_lines_note(det_verdict, commit, changed_files, branch_ref):
    """For the auditor, add the decisive 'removed lines provably absent' signal
    when it applies, so the model commits to a verdict instead of hedging."""
    if (
        det_verdict == "affected"
        and buggy_lines_still_present(commit, changed_files, branch_ref) is False
    ):
        return _PREIMAGE_ABSENT_NOTE
    return ""


def build_user_prompt(
    commit, branch, branch_ref, changed_files, bug_commits, det_verdict
):
    """Assemble the user message: fix diff + branch file context + absence /
    symbol / deleted-line signals + the role-specific task block."""
    file_context, absent_files, any_present = branch_file_context(
        commit, branch, branch_ref, changed_files
    )
    commit_list = ", ".join(list(bug_commits)[:5]) or "(none found)"
    task = (
        _AUDITOR_TASK.format(branch=branch)
        if det_verdict == "affected"
        else _TIEBREAKER_TASK
    )
    return (
        f"## Impact Analysis Request\n\n"
        f"**Fix commit:** `{commit}`\n"
        f"**Target branch:** `{branch}`\n"
        f"**Commit(s) that wrote these lines:** {commit_list}\n\n"
        f"### Patch diff (what the fix changes on main)\n"
        f"```diff\n{get_commit_diff(commit)}\n```\n\n"
        f"### Relevant files on the target branch\n"
        f"{file_context}"
        f"{absence_note(absent_files, any_present)}"
        f"{symbol_presence(commit, changed_files, branch_ref)}"
        f"{buggy_lines_note(det_verdict, commit, changed_files, branch_ref)}\n\n"
        f"{task}"
    )


def call_model(client, user):
    """Stream the model and return the final text, or None on API failure."""
    try:
        with client.messages.stream(
            model=MODEL_ID,
            max_tokens=MAX_TOKENS,
            thinking={"type": "adaptive"},
            system=_SYSTEM_PROMPT,
            messages=[{"role": "user", "content": user}],
        ) as stream:
            response = stream.get_final_message()
    except Exception as exc:
        print(f"[ai_impact_analysis] API call failed: {exc}", file=sys.stderr)
        return None
    return "".join(
        block.text for block in response.content if hasattr(block, "text")
    ).strip()


def parse_verdict(raw):
    """Pull (likely_affected, confidence) from the model's structured reply."""
    likely, confidence = None, "low"
    for line in raw.splitlines():
        ll = line.lower()
        if "likely affected" in ll:
            if "yes" in ll:
                likely = True
            elif "no" in ll:
                likely = False  # else leave None (uncertain)
        if "confidence" in ll:
            for level in ("high", "medium", "low"):
                if level in ll:
                    confidence = level
                    break
    return likely, confidence


def ai_impact_analysis(
    commit, branch, changed_files, bug_commits, det_verdict="inconclusive"
):
    """Advisory: ask Claude whether *branch* is affected by the fix in *commit*.

    Role is selected by *det_verdict*: "affected" -> AUDITOR (look for an
    oldest-commit false positive), "inconclusive" -> TIE-BREAKER (second
    opinion). ADVISORY ONLY -- never auto-applied. Returns a dict with keys
    likely_affected (True/False/None), confidence, reasoning, raw_advisory; or
    None if the SDK/credentials or the API call are unavailable.
    """
    client = ai_client()
    if client is None:
        return None
    branch_ref = f"origin/{branch}"
    user = build_user_prompt(
        commit, branch, branch_ref, changed_files, bug_commits, det_verdict
    )
    raw = call_model(client, user)
    if raw is None:
        return None
    likely, confidence = parse_verdict(raw)
    return {
        "likely_affected": likely,
        "confidence": confidence,
        "reasoning": raw,
        "raw_advisory": _ADVISORY_WRAP.format(raw=raw),
    }


# --------------------------------------------------------------------------
# Resolution pass 1: decide the UNSURE branches
# --------------------------------------------------------------------------


def decide_unsure_branches(
    fix_sha: str,
    files: Sequence[str],
    bug_commits: Sequence[str],
    buckets: Dict[str, str],
    use_ai: bool = True,
) -> "Tuple[Dict[str, str], Dict[str, str], Dict[str, str]]":
    """Turn every UNSURE branch into a definite AFFECTED / NOT_AFFECTED verdict.

    The deterministic pass leaves a branch UNSURE when the fixed code is present
    but ancestry/fingerprint can't confirm the bug commit reached it. Rather than
    show that to the user, consult the AI advisory to decide.

    Safety: if the AI is uncertain, returns no answer, or is unavailable, the
    branch resolves to AFFECTED (flagged for review), never NOT_AFFECTED. So the
    automatic resolution can only over-flag, never create a silent miss.

    Returns ``(buckets, decided_by, summaries)``. ``decided_by[branch]`` is a
    one-line basis; ``summaries[branch]`` is the AI's reasoning where it judged.
    """
    decided_by: Dict[str, str] = {b: "deterministic" for b in buckets}
    summaries: Dict[str, str] = {}
    unsure = [b for b, s in buckets.items() if s == UNSURE]
    for branch in unsure:
        adv = (
            ai_impact_analysis(fix_sha, branch, files, set(bug_commits))
            if use_ai
            else None
        )
        if adv is None:
            buckets[branch] = AFFECTED
            decided_by[branch] = (
                "inconclusive, --no-ai -> flagged for review"
                if not use_ai
                else "inconclusive, AI unavailable -> flagged for review"
            )
        elif adv.get("likely_affected") is True:
            buckets[branch] = AFFECTED
            decided_by[branch] = f"AI: likely affected ({adv.get('confidence')})"
            summaries[branch] = adv.get("reasoning", "").strip()
        elif adv.get("likely_affected") is False:
            buckets[branch] = NOT_AFFECTED
            decided_by[branch] = f"AI: likely not affected ({adv.get('confidence')})"
            summaries[branch] = adv.get("reasoning", "").strip()
        else:
            buckets[branch] = AFFECTED
            decided_by[branch] = (
                f"AI: uncertain ({adv.get('confidence')}) -> flagged for review"
            )
            summaries[branch] = adv.get("reasoning", "").strip()
    return buckets, decided_by, summaries


# --------------------------------------------------------------------------
# Resolution pass 2: review suspicious AFFECTED branches (advisory only)
# --------------------------------------------------------------------------


def commit_time(sha: str) -> int:
    """Unix commit timestamp of *sha* (0 if it can't be resolved). Used to pick
    the newest bug commit."""
    out = git("show", "-s", "--format=%ct", sha, check=False).stdout.strip()
    return int(out) if out.isdigit() else 0


def likely_over_flagged(
    bug_commits: Sequence[str], buckets: Dict[str, str]
) -> "Dict[str, Tuple[int, int]]":
    """AFFECTED branches that look like over-flags worth a second opinion.

    A branch is bucketed AFFECTED as soon as one bug commit reaches it. When the
    fix also touches old, shared code (e.g. lines tracing back to the initial
    import), that lone match can be ancient and present on branches that predate
    the actual vulnerability -- the documented over-flag.

    The signal: the branch is missing the NEWEST bug commit (the commit most
    likely to have written the actual bug) while still having some older lineage.
    A genuinely affected branch has that newest commit; one that predates the
    vulnerability does not. Returns ``{branch: (present_count, total)}`` for each
    candidate. Deterministic, no AI.
    """
    intro = list(bug_commits)
    suspects: "Dict[str, Tuple[int, int]]" = {}
    if len(intro) < 2:
        # A single bug commit that reaches the branch is an unambiguous hit;
        # there is no old-vs-new lineage split to be suspicious about.
        return suspects
    newest = max(intro, key=commit_time)
    intro_set = set(intro)
    for branch, state in buckets.items():
        if state != AFFECTED:
            continue
        present = bug_commits_present(intro_set, branch)
        if present and newest not in present:
            suspects[branch] = (len(present), len(intro))
    return suspects


def add_over_flag_notes(
    fix_sha: str,
    files: Sequence[str],
    bug_commits: Sequence[str],
    suspects: "Dict[str, Tuple[int, int]]",
    decided_by: Dict[str, str],
    summaries: Dict[str, str],
    use_ai: bool = True,
) -> None:
    """Attach a false-positive review note to over-flag-candidate AFFECTED
    branches (those from :func:`likely_over_flagged`), consulting the AI
    advisory when *use_ai*.

    CRITICAL: this is advisory only and NEVER changes the verdict. The branch
    stays AFFECTED even if the AI thinks it is a false positive -- we only
    annotate it for human review. So widening AI coverage here can reduce noise
    but can never turn a real hit into a silent miss (no false negatives).
    """
    intro = set(bug_commits)
    for branch, (present, total) in suspects.items():
        note = (
            f"matched {present}/{total} commits that wrote these lines; newest absent "
            "-> possible false positive, review"
        )
        if use_ai:
            adv = ai_impact_analysis(fix_sha, branch, files, intro)
            if adv is not None:
                conf = adv.get("confidence")
                if adv.get("likely_affected") is False:
                    note = (
                        "AFFECTED (deterministic) but AI suspects FALSE POSITIVE "
                        f"({conf}) -> confirm before skipping"
                    )
                elif adv.get("likely_affected") is True:
                    note = f"affected; AI confirms ({conf})"
                else:
                    note = f"affected; AI uncertain ({conf}) -> review"
                summaries[branch] = adv.get("reasoning", "").strip()
        decided_by[branch] = note


def refine_with_ai(args, fix_sha, files, bug_commits, buckets):
    """Decide the UNSURE branches via the AI advisory (unless --no-ai), then add a
    review note to any suspicious AFFECTED branches.

    Returns ``(buckets, decided_by, summaries)``, printing a one-line notice when
    the AI is about to be consulted.
    """
    unsure = [b for b, s in buckets.items() if s == UNSURE]
    use_ai = not args.no_ai
    if unsure and use_ai and not args.json:
        print(
            f"{len(unsure)} branch(es) inconclusive by git history; "
            f"consulting AI to decide...\n",
            file=sys.stderr,
        )
    buckets, decided_by, summaries = decide_unsure_branches(
        fix_sha, files, bug_commits, buckets, use_ai=use_ai
    )

    # Second pass: AFFECTED branches matched only by a partial bug commit lineage
    # are likely over-flags (old shared code present, newer vulnerable commit
    # absent). Flag them for review -- consulting AI when enabled -- but never
    # change the verdict, so this can only reduce noise, never cause a miss.
    suspects = likely_over_flagged(bug_commits, buckets)
    if suspects:
        if use_ai and not args.json:
            print(
                f"{len(suspects)} AFFECTED branch(es) match only part of the fix's "
                "lineage (possible over-flag); consulting AI for a review note...\n",
                file=sys.stderr,
            )
        add_over_flag_notes(
            fix_sha, files, bug_commits, suspects, decided_by, summaries, use_ai=use_ai
        )
    return buckets, decided_by, summaries
