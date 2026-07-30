"""
The `resolve` command: fix backport conflicts by hand, one branch at a time.

Given a fix (`--commit` or `--pr`), find the affected release branches and, for each
one whose cherry-pick conflicts, check that branch out in your own repo with the
conflict live so you can edit it in your IDE. Files you clean up get staged for you;
anything still holding conflict markers is reported. `git rerere` is on, so fixing a
conflict once reuses it on sibling branches like the FIPS twins. At the end it can
push and open one PR per resolved branch.

Your original branch is restored afterwards -- unless you bailed out partway, in
which case the repo is left on the unfinished branch so you can finish by hand.

Clean cherry-picks are skipped here on purpose: `publish` and `apply` already open
those, and re-opening them would clash on the branch name. `resolve` handles exactly
the branches they reported as conflicts. `run_resolution` is also what `apply` calls
when a cherry-pick conflicts.
"""

import json
import os
import re
import sys

from engine.analysis import get_supported_branches, sort_branches
from commands.publish import assert_fork_remote, gh, plan_marker, summary_table
from util.config import AFFECTED, BackportError
from util.git import (
    BOT_IDENTITY,
    enable_rerere,
    file_has_conflict_markers,
    git,
    ref_exists,
    repo_path,
    resolve_commit,
    unmerged_files,
)
from util.render import ask_yn, print_section, print_summary
from engine.ai import refine_with_ai
from engine.analysis import analyze_branches


# --- Resolving which fix to backport --------------------------------------


def pr_commit(pr: str, remote: str) -> str:
    """Resolve a PR number to a backportable commit-ish via ``gh``.

    A merged PR resolves to its merge/squash commit; an open PR to its head
    commit. If the commit is not present locally we fetch it from *remote* first
    (a merge commit, or the ``pull/<n>/head`` ref for an open PR).
    """
    info = gh(
        "pr", "view", str(pr), "--json", "state,mergeCommit,headRefOid", check=False
    )
    if info.returncode != 0:
        raise BackportError(
            f"could not read PR #{pr}: {(info.stderr or info.stdout).strip()}"
        )
    data = json.loads(info.stdout or "{}")
    merge = (data.get("mergeCommit") or {}).get("oid")
    if merge:
        if not ref_exists(merge):
            git("fetch", remote, merge, check=False)
        return merge
    head = data.get("headRefOid")
    if not head:
        raise BackportError(f"PR #{pr} has no resolvable commit.")
    if not ref_exists(head):
        git("fetch", remote, f"pull/{pr}/head", check=False)
    return head


def resolve_fix_and_subject(args) -> "tuple[str, str]":
    """Return ``(fix_sha, subject)`` for the fix named by ``--commit`` or ``--pr``."""
    if getattr(args, "commit", None):
        return resolve_commit(args.commit)
    if getattr(args, "pr", None):
        return resolve_commit(pr_commit(args.pr, args.remote))
    raise BackportError("resolve needs --commit <sha> or --pr <number>.")


# --- Interactive per-branch conflict walk ---------------------------------


def cherry_pick_in_progress(wt: str) -> bool:
    """True if a cherry-pick is still in progress in *wt* (CHERRY_PICK_HEAD exists).
    False once the user (or we) run ``git cherry-pick --continue``/``--abort``."""
    return (
        git(
            "rev-parse", "-q", "--verify", "CHERRY_PICK_HEAD", check=False, cwd=wt
        ).returncode
        == 0
    )


def stage_resolved(wt: str) -> "list[str]":
    """Stage every unmerged file that no longer contains conflict markers, and
    return the paths that STILL have markers (i.e. not yet resolved).

    This is how we let the user just edit files in the shell without needing to
    ``git add`` -- anything they've cleaned up gets staged for them, and anything
    still holding ``<<<<<<<`` / ``>>>>>>>`` markers is reported back so we never
    continue the cherry-pick with an unresolved file.
    """
    still: "list[str]" = []
    for f in unmerged_files(wt):
        if file_has_conflict_markers(os.path.join(wt, f["path"])):
            still.append(f["path"])
        else:
            git("add", "--", f["path"], cwd=wt)
    return still


def conflict_lines(files: "list[dict]") -> "list[str]":
    """git-status-style, aligned list lines, one per file:
    ``    both modified:   crypto/fipsmodule/dh/dh.c`` (full repo-relative path)."""
    width = max((len(f["kind"]) for f in files), default=0) + 1
    return [f"    {(f['kind'] + ':'):<{width}}  {f['path']}" for f in files]


def split_conflicts(conflicts: "list[dict]", root: str) -> "tuple[list, list]":
    """Split unmerged files into (need_editing, rerere_applied): the ones that
    still carry `<<<<<<<` markers vs the ones rerere already resolved."""
    marker_paths = {
        c["path"]
        for c in conflicts
        if file_has_conflict_markers(os.path.join(root, c["path"]))
    }
    need = [c for c in conflicts if c["path"] in marker_paths]
    rerere = [c for c in conflicts if c["path"] not in marker_paths]
    return need, rerere


def current_ref() -> str:
    """The branch name currently checked out, or the raw SHA if detached."""
    r = git("symbolic-ref", "--quiet", "--short", "HEAD", check=False)
    if r.returncode == 0 and r.stdout.strip():
        return r.stdout.strip()
    return git("rev-parse", "HEAD").stdout.strip()


def resolve_branch(
    fix_sha: str, branch: str, run_id: str, repo: str
) -> "tuple[str, str]":
    """Cherry-pick *fix_sha* onto ``origin/<branch>``, letting the user fix conflicts.

    The branch is checked out in the user's own repo so their IDE shows the conflict;
    the caller puts them back on their original branch afterwards.

    Returns ``(status, detail)``:
      clean   -> no conflict, so `publish`/`apply` own it; skipped here
      ready   -> conflicts resolved and committed, on *detail*
      blocked -> left unresolved; the repo stays on the branch to finish by hand
      error   -> *detail* is the message
    """
    ref = f"origin/{branch}"
    if not ref_exists(ref):
        return "error", f"{ref} not found"
    local_branch = f"backport/{branch}/{run_id}"
    co = git("checkout", "--quiet", "--detach", ref, check=False)
    if co.returncode != 0:
        return "error", f"could not check out {ref}: {(co.stderr or co.stdout).strip()}"

    pick = git("cherry-pick", fix_sha, check=False)
    if pick.returncode == 0:
        # Clean -> publish/apply own it; skip. The commit sits on detached HEAD and is
        # discarded when we check out the next branch / restore the original.
        print("  No conflicts — clean cherry-pick (publish opens this backport).")
        return "clean", None

    base_sha = git("rev-parse", ref).stdout.strip()
    need, rerere = split_conflicts(unmerged_files(repo), repo)
    print("  This backport has conflicts that must be resolved.\n")
    print("  Checked out in your working tree — edit these in your IDE:")
    print(f"    {repo}\n")
    if need:
        print("  Conflicting files:")
        for line in conflict_lines(need):
            print(line)
        print()
    if rerere:
        print("  Auto-resolved by rerere — please verify:")
        for line in conflict_lines(rerere):
            print(line)
        print()
    if not need:
        print("  Nothing to edit — rerere resolved everything; just confirm.\n")

    while True:
        if not ask_yn(f"  Have you resolved the conflicts on {branch}?"):
            print(
                f"  Left checked out on {branch} to finish by hand:\n"
                "    git add -A && git cherry-pick --continue   # when done\n"
                "    git cherry-pick --abort                    # to bail out"
            )
            return "blocked", branch
        if not cherry_pick_in_progress(repo):
            head = git("rev-parse", "HEAD").stdout.strip()
            if head == base_sha:
                print("  Skipped — cherry-pick was aborted.")
                return "blocked", branch
            break  # user ran --continue themselves
        still = stage_resolved(repo)
        if not still:
            break
        print("  Still unresolved (conflict markers remain):")
        for path in still:
            print(f"    {path}")
        print("  Fix them, then answer again.")

    if cherry_pick_in_progress(repo):
        cont = git(
            *BOT_IDENTITY,
            "-c",
            "core.editor=true",
            "cherry-pick",
            "--continue",
            check=False,
        )
        if cont.returncode != 0:
            print("  `git cherry-pick --continue` failed.")
            return "blocked", branch
    new_sha = git("rev-parse", "HEAD").stdout.strip()
    git("branch", "-f", local_branch, new_sha)
    print(f"  ✓ All conflicts resolved on {branch} — backport ready.")
    return "ready", local_branch


# --- Opening a PR for a ready branch --------------------------------------


def open_pr(
    branch: str, local_branch: str, fix_sha: str, subject: str, source_pr, remote: str
) -> str:
    """Push *local_branch* to the fork and open a normal PR into the release
    branch. Returns the PR URL or an ``"error: ..."`` string."""
    link = f" of #{source_pr}" if source_pr else ""
    title = f"[backport {branch}] {subject}"
    body = (
        f"Backport{link} (`{fix_sha[:12]}`) onto `{branch}`, with merge conflicts "
        "resolved locally.\n\n"
        "- Impact verdict: **AFFECTED**.\n"
        "- **Not** auto-merged -- please review the conflict resolution before "
        "merging.\n\n"
        "_Opened by the AWS-LC backport bot (`backport resolve`)._"
    )
    push = git(
        "push",
        "--force-with-lease",
        remote,
        f"{local_branch}:{local_branch}",
        check=False,
    )
    if push.returncode != 0:
        return f"error: push failed: {(push.stderr or push.stdout).strip()}"
    pr = gh(
        "pr",
        "create",
        "--base",
        branch,
        "--head",
        local_branch,
        "--title",
        title,
        "--body",
        body,
        check=False,
    )
    if pr.returncode != 0:
        return f"error: gh pr create failed: {(pr.stderr or pr.stdout).strip()}"
    return pr.stdout.strip()


def find_open_pr_url(head: str) -> "str | None":
    """URL of the open PR whose head branch is *head*, or None. Used to relink the
    clean backport PRs `publish` already opened when we rebuild the summary."""
    r = gh(
        "pr",
        "list",
        "--head",
        head,
        "--state",
        "open",
        "--json",
        "url",
        "-q",
        ".[0].url",
        check=False,
    )
    return r.stdout.strip() or None


def post_resolution_summary(
    pr,
    fix_sha,
    subject,
    buckets,
    created,
    clean_skipped,
    still_conflicting,
    errors,
    run_id,
) -> None:
    """Post an updated, publish-style summary comment on the source PR after resolving.

    Same table format as `publish`, but the previously-conflicting branches now show
    their freshly opened backport PR (✅) instead of a merge-conflict warning.
    """
    outcomes: dict = {}
    for branch, url in created.items():
        outcomes[branch] = ("opened", url)
    for branch in clean_skipped:
        url = find_open_pr_url(f"backport/{branch}/{run_id}")
        outcomes[branch] = ("opened", url) if url else ("done", None)
    for branch in still_conflicting:
        outcomes[branch] = ("error", "still needs resolution")
    for branch, msg in errors.items():
        outcomes[branch] = ("error", msg)
    table = summary_table(fix_sha, subject, buckets, outcomes, source_pr=pr)
    body = (
        "🔧 **Updated after `backport resolve`** — conflicts resolved locally; "
        "backport PRs opened for the previously-conflicting branches.\n\n"
        + table
        + "\n\n"
        + plan_marker(fix_sha, subject, buckets, outcomes)
    )
    gh("pr", "comment", str(pr), "--body", body, check=False)


# The plan is attached to the summary comment as a fenced ```json block``` (see
# publish.plan_marker). Grab the contents of every such block; we then pick the last
# one carrying our sentinel key.
_PLAN_RE = re.compile(r"```json\s*\n(.*?)\n```", re.DOTALL)


def parse_plan(comments_text: str) -> "dict | None":
    """Pick the newest valid, sentinel-bearing backport-bot plan out of raw PR
    comment text. Pure (no ``gh``) so it can be unit-tested; ``read_bot_plan``
    feeds it the concatenated comment bodies.

    Scans every fenced ``json`` block and returns the last one that parses and
    carries the ``backport_bot_plan`` sentinel -- so a later resolve-run summary
    supersedes the original publish one, and an unrelated ``json`` block (or the
    ``bash`` command block) is ignored.
    """
    for blob in reversed(_PLAN_RE.findall(comments_text)):  # newest comment wins
        try:
            obj = json.loads(blob)
        except json.JSONDecodeError:
            continue
        if isinstance(obj, dict) and obj.get("backport_bot_plan"):
            return obj
    return None


def read_bot_plan(pr) -> "dict | None":
    """Read the backport bot's machine-readable plan from the summary comment(s)
    on *pr*, so we can target exactly the branches `publish` flagged without re-running
    the impact analysis. Returns the parsed dict, or None if no plan is present
    (then the caller falls back to computing it locally).

    The plan is a fenced ``json`` block tagged with a ``backport_bot_plan``
    sentinel key (``publish.plan_marker``); the actual selection is done by the pure
    :func:`parse_plan`.
    """
    r = gh(
        "pr",
        "view",
        str(pr),
        "--json",
        "comments",
        "-q",
        ".comments[].body",
        check=False,
    )
    if r.returncode != 0:
        return None
    return parse_plan(r.stdout)


# --- Command --------------------------------------------------------------


def run_resolution(
    args,
    fix_sha,
    subject,
    buckets,
    targets,
    source_pr,
    preopened=(),
    clean_local=(),
) -> int:
    """Resolve *targets*, then open one PR per branch that's ready.

    Used by both entry points:
      cmd_resolve -- *targets* are the conflicting branches; *preopened* are ones
                     `publish` already opened PRs for (listed in the summary only).
      apply       -- *targets* are the branches that just conflicted, and
                     *clean_local* the ones it picked cleanly. Both get PRs.

    *source_pr*, if given, gets the updated summary comment.
    """
    if not sys.stdin.isatty():
        print(
            "\nresolve is interactive; run it in a terminal (not a pipe/CI).",
            file=sys.stderr,
        )
        return 3

    remote = getattr(args, "remote", "origin")
    run_id = fix_sha[:8]
    enable_rerere()
    original_ref = None
    left_on_branch = None
    resolved: "dict[str, str]" = {}
    clean_skipped: "list[str]" = list(preopened)
    errors: "dict[str, str]" = {}

    if targets:
        # Each branch is checked out in the user's own repo, so the tree must be
        # clean and we have to remember where to put them back.
        if git("status", "--porcelain").stdout.strip():
            raise BackportError(
                "resolving conflicts checks each branch out in your current repo, "
                "so it needs a clean working tree. Commit or stash your changes "
                "first."
            )
        original_ref = current_ref()
        if os.path.abspath(__file__).startswith(os.path.abspath(repo_path()) + os.sep):
            print(
                "note: the tool lives inside the target repo, so `util/backport/` is "
                "briefly removed while a release branch is checked out (restored at "
                "the end). To avoid that, run from a separate clone with --repo."
            )

        print(f"\n{len(targets)} branch(es) have conflicts to resolve:")
        for b in targets:
            print(f"  - {b}")
        print("\nrerere is on: a resolution is reused across identical conflicts on")
        print("sibling branches (you'll be asked to verify those).")

        for branch in targets:
            print(f"\n── {branch} " + "─" * max(0, 50 - len(branch)))
            status, detail = resolve_branch(fix_sha, branch, run_id, repo_path())
            if status == "clean":
                clean_skipped.append(branch)
            elif status == "ready":
                resolved[branch] = detail
            elif status == "blocked":
                # Left checked out for the user to finish; stop here rather than
                # checking another branch out on top of their half-done work.
                left_on_branch = branch
                break
            else:
                errors[branch] = detail
                print(f"   error: {detail}")

        if original_ref and not left_on_branch:
            git("checkout", "--quiet", original_ref, check=False)

    # Everything that should get a PR: freshly resolved conflicts + the branches
    # apply already cherry-picked cleanly (their backport/<b>/<run_id> exists).
    to_pr: "dict[str, str]" = dict(resolved)
    for b in clean_local:
        to_pr.setdefault(b, f"backport/{b}/{run_id}")

    print("\n" + "─" * 52)
    print("Summary\n")
    print_section("Ready to open PRs", to_pr or ["(none)"])
    if clean_skipped:
        print_section("Already opened by publish", clean_skipped)
    if left_on_branch:
        print_section("Left checked out to finish (re-run when done)", [left_on_branch])
    if errors:
        print_section("Errors", [f"{b}: {m}" for b, m in errors.items()])

    if not to_pr:
        print("Nothing to open PRs for.")
        return 0

    if not ask_yn(f"Open {len(to_pr)} pull request(s)?"):
        print("Skipped. Local branches kept:")
        for b, lb in to_pr.items():
            print(f"  - {lb}")
        return 0

    assert_fork_remote(remote)  # only gate the push, so local resolution always works
    print()
    created: "dict[str, str]" = {}
    for branch, local_branch in to_pr.items():
        url = open_pr(branch, local_branch, fix_sha, subject, source_pr, remote)
        print(f"  {branch}\n    {url}")
        if not url.startswith("error:"):
            created[branch] = url

    # Post an updated publish-style summary on the source PR: the previously-conflicting
    # branches now show their opened backport PR instead of a conflict warning.
    still_conflicting = [left_on_branch] if left_on_branch else []
    if source_pr and created:
        post_resolution_summary(
            source_pr,
            fix_sha,
            subject,
            buckets,
            created,
            clean_skipped,
            still_conflicting,
            errors,
            run_id,
        )
        print(f"\nUpdated the summary on #{source_pr}.")
    return 0


def cmd_resolve(args) -> int:
    """Interactively resolve backport conflicts and open one PR per branch."""
    # Prefer the backport bot's own summary on the PR: it already ran the impact
    # analysis (AI) in CI, so reading its plan avoids a second AI pass and targets
    # exactly the branches it flagged. Fall back to computing locally when there is
    # no such comment (e.g. --commit with no PR) or when --reanalyze is given.
    plan = None
    if getattr(args, "pr", None) and not getattr(args, "reanalyze", False):
        plan = read_bot_plan(args.pr)

    if plan:
        fix_sha = plan.get("fix") or resolve_fix_and_subject(args)[0]
        subject = plan.get("subject", "")
        branch_info = plan.get("branches", {})
        buckets = {b: info.get("impact", AFFECTED) for b, info in branch_info.items()}
        targets = sort_branches(
            b for b, info in branch_info.items() if info.get("outcome") == "conflict"
        )
        # Branches publish already opened clean PRs for -- carry them into the final
        # summary so it stays complete (relinked to their existing PRs).
        preopened = [
            b
            for b, info in branch_info.items()
            if info.get("outcome") in ("opened", "done")
        ]
        if not ref_exists(fix_sha):
            git("fetch", args.remote, fix_sha, check=False)
        print(
            f"Using the backport bot's summary from #{args.pr} "
            f"(no re-analysis): {len(targets)} conflicting branch(es) to resolve."
        )
        if not targets:
            print("Nothing left to resolve on that PR.")
            return 0
    else:
        fix_sha, subject = resolve_fix_and_subject(args)
        branches = sort_branches(get_supported_branches())
        if not branches:
            raise BackportError(
                "no supported release branches found (is this an AWS-LC clone with "
                "the release branches fetched? `git fetch origin`)."
            )
        files, bug_commits, buckets = analyze_branches(fix_sha, branches)
        buckets, decided_by, _ = refine_with_ai(
            args, fix_sha, files, bug_commits, buckets
        )
        print_summary(fix_sha, files, bug_commits, buckets, decided_by)
        targets = sort_branches(b for b, s in buckets.items() if s == AFFECTED)
        preopened = []
        if not targets:
            print("\nNo AFFECTED branches; nothing to resolve.")
            return 0

    return run_resolution(
        args,
        fix_sha,
        subject,
        buckets,
        targets,
        source_pr=getattr(args, "pr", None),
        preopened=preopened,
    )
