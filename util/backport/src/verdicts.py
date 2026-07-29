"""
Verdict computation.

Layer: analysis. Builds on ``engine`` + ``ai`` + ``gitutil``; the shared
classification step every command (``analyze`` / ``apply`` / ``ci`` / ``resolve``)
runs to turn a fix into per-branch verdicts.

The deterministic classifier (:func:`analyze_branches`) sorts every branch into
AFFECTED / NOT_AFFECTED / UNSURE / ALREADY using ancestry, patch-id, and the
vulnerable pre-image. Then the advisory AI passes (:func:`resolve_inconclusive`)
decide the UNSURE branches and annotate suspicious AFFECTED ones -- always in a
direction that can add review noise but never cause a silent miss.
"""

import os
import sys
from typing import Dict, List, Sequence, Tuple

import engine as bot
from ai import ai_impact_analysis
from common import AFFECTED, ALREADY, NOT_AFFECTED, UNSURE
from gitutil import branch_basenames, changed_files_with_status, git


# --------------------------------------------------------------------------
# Deterministic bucketing (no AI)
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
    # Path 1 + Path 2: does an introducer reach the branch by SHA ancestry or
    # patch-id equivalence?
    affected = bot.introducer_reaches(introducers, ref)
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
    preimage = bot.vulnerable_preimage_present(fix_sha, src_files, ref)
    if affected and preimage is not False:
        return ALREADY if bot.is_already_patched(fix_sha, branch) else AFFECTED
    # Path 2b: ancestry/patch-id missed (a branch-specific introducer), but the
    # exact removed lines ARE present -> deterministically AFFECTED.
    if not affected and preimage is True:
        return AFFECTED
    # Not confidently affected. Decide UNSURE vs a confident NOT AFFECTED,
    # biasing hard toward UNSURE so a miss is never silent.
    present = any(
        bot.get_file_on_branch(f, ref, commit=fix_sha)[0] is not None for f in src_files
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
    return [f for f in files if not bot.is_test_or_generated_file(f)] or list(files)


def analyze_branches(
    fix_sha: str, branches: Sequence[str]
) -> "Tuple[List[str], List[str], Dict[str, str]]":
    """Classify each branch deterministically (no AI).

    Returns ``(changed_files, sorted_introducers, buckets)``, where buckets maps
    each branch to one of AFFECTED / NOT_AFFECTED / UNSURE / ALREADY. The per-branch
    decision lives in :func:`classify_branch`.
    """
    files, introducer_files = changed_files_with_status(fix_sha)
    introducers = bot.find_introducing_commit(fix_sha, introducer_files)
    src_files = source_files(files)
    buckets = {
        branch: classify_branch(fix_sha, src_files, introducers, branch)
        for branch in branches
    }
    return files, sorted(introducers), buckets


# --------------------------------------------------------------------------
# AI resolution pass 1: decide the UNSURE branches
# --------------------------------------------------------------------------


def resolve_unsure(
    fix_sha: str,
    files: Sequence[str],
    introducers: Sequence[str],
    buckets: Dict[str, str],
    use_ai: bool = True,
) -> "Tuple[Dict[str, str], Dict[str, str], Dict[str, str]]":
    """Turn every UNSURE branch into a definite AFFECTED / NOT_AFFECTED verdict.

    The deterministic pass leaves a branch UNSURE when the fixed code is present
    but ancestry/patch-id can't confirm the introducer reached it. Rather than
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
            ai_impact_analysis(fix_sha, branch, files, set(introducers))
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
# AI resolution pass 2: review suspicious AFFECTED branches (advisory only)
# --------------------------------------------------------------------------


def commit_time(sha: str) -> int:
    """Unix commit timestamp of *sha* (0 if it can't be resolved). Used to pick
    the newest introducer."""
    out = git("show", "-s", "--format=%ct", sha, check=False).stdout.strip()
    return int(out) if out.isdigit() else 0


def suspect_affected_branches(
    introducers: Sequence[str], buckets: Dict[str, str]
) -> "Dict[str, Tuple[int, int]]":
    """AFFECTED branches that look like over-flags worth a second opinion.

    A branch is bucketed AFFECTED as soon as one introducer reaches it. When the
    fix also touches old, shared code (e.g. lines tracing back to the initial
    import), that lone match can be ancient and present on branches that predate
    the actual vulnerability -- the documented over-flag.

    The signal: the branch is missing the NEWEST introducer (the commit most
    likely to have written the actual bug) while still having some older lineage.
    A genuinely affected branch has that newest commit; one that predates the
    vulnerability does not. Returns ``{branch: (present_count, total)}`` for each
    candidate. Deterministic, no AI.
    """
    intro = list(introducers)
    suspects: "Dict[str, Tuple[int, int]]" = {}
    if len(intro) < 2:
        # A single introducer that reaches the branch is an unambiguous hit;
        # there is no old-vs-new lineage split to be suspicious about.
        return suspects
    newest = max(intro, key=commit_time)
    intro_set = set(intro)
    for branch, state in buckets.items():
        if state != AFFECTED:
            continue
        present = bot.present_introducers(intro_set, branch)
        if present and newest not in present:
            suspects[branch] = (len(present), len(intro))
    return suspects


def review_suspect_affected(
    fix_sha: str,
    files: Sequence[str],
    introducers: Sequence[str],
    suspects: "Dict[str, Tuple[int, int]]",
    decided_by: Dict[str, str],
    summaries: Dict[str, str],
    use_ai: bool = True,
) -> None:
    """Attach a false-positive review note to over-flag-candidate AFFECTED
    branches (those from :func:`suspect_affected_branches`), consulting the AI
    advisory when *use_ai*.

    CRITICAL: this is advisory only and NEVER changes the verdict. The branch
    stays AFFECTED even if the AI thinks it is a false positive -- we only
    annotate it for human review. So widening AI coverage here can reduce noise
    but can never turn a real hit into a silent miss (no false negatives).
    """
    intro = set(introducers)
    for branch, (present, total) in suspects.items():
        note = (
            f"affected via {present}/{total} introducers; newer commit(s) absent "
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


def resolve_inconclusive(args, fix_sha, files, introducers, buckets):
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
    buckets, decided_by, summaries = resolve_unsure(
        fix_sha, files, introducers, buckets, use_ai=use_ai
    )

    # Second pass: AFFECTED branches matched only by a partial introducer lineage
    # are likely over-flags (old shared code present, newer vulnerable commit
    # absent). Flag them for review -- consulting AI when enabled -- but never
    # change the verdict, so this can only reduce noise, never cause a miss.
    suspects = suspect_affected_branches(introducers, buckets)
    if suspects:
        if use_ai and not args.json:
            print(
                f"{len(suspects)} AFFECTED branch(es) match only part of the fix's "
                "lineage (possible over-flag); consulting AI for a review note...\n",
                file=sys.stderr,
            )
        review_suspect_affected(
            fix_sha, files, introducers, suspects, decided_by, summaries, use_ai=use_ai
        )
    return buckets, decided_by, summaries
