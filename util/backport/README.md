# AWS-LC Backport

Works out which supported release branches still need a fix, before it merges, and
cherry-picks it onto the ones that do.

## What This Tool Does

Given a fix on your branch (or any commit), `analyze` decides for every supported
FIPS release branch whether that branch still needs the fix. It does this in two
passes:

1. **Git history** - finds the distinctive lines the fix deletes, blames the commits
   that wrote them, and checks whether those commits and those lines reached each
   branch. This settles most branches on its own.
2. **AI** - only for branches history cannot settle, plus a second look at flagged
   branches that match just part of a fix's history. It answers through a fixed schema
   rather than in prose, and a no-answer always leaves the branch flagged, so it can
   add flags for a human but never hide a needed backport.

It also says when a fix reaches inside the validated FIPS module, which is a
certification question rather than a code one.

`apply` then cherry-picks the fix onto one local branch per affected branch, and
`publish` turns those into one pull request each.

Nothing is auto-merged, and nothing is ever a draft. Every pull request needs review.

## Prerequisites

### Required Tools

- **Python 3**: for the tool itself
- **git**: with the release branches fetched from the remote that has them
  (`git fetch upstream`, or `git fetch origin` in a clone of `aws/aws-lc` itself)
- **anthropic + boto3**: required, not optional (`pip3 install --user anthropic boto3`).
  The AI pass is part of how a verdict is reached, so the tool imports them at startup
  even when `BACKPORT_DISABLE_AI` is set
- **gh**: the GitHub CLI, for `publish` only. Logged in with `gh auth login`, or
  `GH_TOKEN` set, which is how CI supplies it

### AWS Permissions

The AI pass calls Claude on Amazon Bedrock, so you need permission to invoke the
model named in `.github/workflows/ai-config.json`. Credentials are read through the
normal AWS chain (environment, `~/.aws`, SSO, IAM role).

## Setup

Run from the top of an AWS-LC checkout. The tool operates on the checkout it lives
in, so there is nothing to configure.

```bash
# make sure the release branches are present. Whichever remote points at
# aws/aws-lc is the one they are read from
git fetch upstream
```

Credentials for the AI pass come from the normal AWS chain, so `AWS_PROFILE` is usually
all you need. The region is not taken from the environment: it comes from `aws_region`
in `.github/workflows/ai-config.json`, so a stray `AWS_REGION` cannot send the model
calls elsewhere.

```bash
export AWS_PROFILE=your-profile
```

## Usage

### Analyze your current branch

```bash
util/backport/backport analyze
```

With no arguments this analyzes your branch's commits since the mainline. Several
commits are read as their net change, so a fix split across commits is judged as a
whole.

### Analyze a specific commit or range

```bash
# one commit
util/backport/backport analyze --commit ac3aee310

# a range
util/backport/backport analyze --commit origin/main..HEAD
```

### Skip the test file prompt

```bash
util/backport/backport analyze --commit ac3aee310 --skip
```

By default the tool shows the test file in your fix and asks you to confirm it
before the slower per-branch work. `--skip` is for scripts.

**Example Output:**

```
Test file in this fix: crypto/dh_extra/dh_test.cc
Is this the test for your fix? [Y/N] y
2 branch(es) unclear from history, asking AI...

Fix commit: ac3aee3104
Changed files: ['crypto/dh_extra/dh_test.cc', 'crypto/dh_extra/params.c', 'crypto/fipsmodule/dh/check.c']
Wrote these lines: ['48cbd69d', '4b55af0f', '95c29f3c', 'df75139b', 'e0dbced4', 'e11c9926']

  branch                   status          basis
  ------------------------ --------------- ----------------------------------------
  fips-2026-06-26-snapshot AFFECTED        git history
  fips-2025-09-12-lts      AFFECTED        git history
  fips-2024-09-27          AFFECTED        AI: likely affected (high)
  fips-NetOS-2024-06-11    already patched git history
  fips-2022-11-02          AFFECTED        affected, AI agrees (medium)
  fips-2021-10-20-1MU      not affected    AI: likely not affected (high)
  fips-2021-10-20          not affected    git history
```

The `basis` column says what decided each branch, so a history result and an AI one
are told apart.

**Verdicts:**

| Verdict | Meaning |
| --- | --- |
| `AFFECTED` | the branch still needs the fix |
| `not affected` | the vulnerable code is provably not there |
| `already patched` | the fix is already on the branch |
| `UNSURE` | only appears if the AI is unreachable and never resolves |

Anything genuinely unclear becomes `AFFECTED` rather than `not affected`. A wrong
"not affected" means a missed security backport, so the tool always errs toward
flagging.

**The FIPS boundary:**

A fix that touches `crypto/fipsmodule/` gets one more line after the table:

```
FIPS BOUNDARY: this fix touches the validated FIPS module (2 file(s):
crypto/fipsmodule/bn/bn.c, crypto/fipsmodule/bn/internal.h). A backport here has
certification consequences: get FIPS review before merging
```

The module is validated as a build of exactly that source, so changing it is not only a
code review. The tool cannot judge the certification impact and does not try; it makes
sure nobody finds out later. The same line is carried into every pull request `publish`
opens and into the summary it posts, so it survives being read by someone who never ran
`analyze`.

### Cherry-pick onto the affected branches

```bash
util/backport/backport apply
```

Reads the last `analyze` run and cherry-picks the fix onto one local branch per
affected branch, named `backport-<release branch>-<fix>`. Branches `analyze` could not
settle are left out, since picking onto one of those would be a guess. `--branch` does
a single branch, including one that was cleared, and `--yes` skips the confirm.

Each pick happens in its own worktree under `.backport-worktrees/`, so the branch you
have checked out never moves and a half-finished cherry-pick can never strand your own
working tree mid-merge. Each branch is cut from the same remote-tracking release branch
`analyze` judged, so the backport is never built on a base the analysis never saw.

**Example Output:**

```
Fix ac3aee3104, analyzed 2026-08-04 14:36:20
Backporting onto 7 branch(es): fips-2026-06-26-snapshot, fips-2025-09-12-lts, ...
Create these local branches? [Y/N] y
  fips-2026-06-26-snapshot: applied, on backport-fips-2026-06-26-snapshot-ac3aee3104
  fips-2025-09-12-lts: applied, on backport-fips-2025-09-12-lts-ac3aee3104
  fips-2022-11-02: CONFLICT in 4 file(s)
      crypto/dh_extra/dh_test.cc
      crypto/fipsmodule/dh/check.c
      resolve in util/backport/.backport-worktrees/backport-fips-2022-11-02-ac3aee3104

2 of 7 applied cleanly
Resolve each conflict in the worktree named above, then 'git cherry-pick --continue' there.
Nothing was pushed. Review each branch before you open a pull request.
```

A clean pick leaves just the branch and removes its worktree. A conflict keeps the
worktree, stopped mid-cherry-pick, so you can resolve it in place. Conflicts are
normal on the older branches, where the surrounding code has moved on.

**Results:**

| Result | Meaning |
| --- | --- |
| `applied` | cherry-picked cleanly, the branch is left behind and its worktree removed |
| `CONFLICT` | the worktree is kept, stopped mid-cherry-pick, for you to resolve |
| `skipped` | that backport branch already exists, so nothing was touched |
| `nothing to do` | the change is already on the branch, so the pick came out empty |

`skipped` is what makes a second run safe: re-running after resolving one conflict
leaves the branches you already have alone. The command exits non-zero if any branch
conflicted, so a script can tell whether anything needs a human.

### Open the pull requests

```bash
util/backport/backport publish
```

Pushes each finished backport branch to your fork and opens one pull request per
branch into the matching release branch. One command, however many branches the fix
touched.

Most of the time you never type it: `apply --open-pr` offers to run it as soon as the
cherry-picks are done, so a normal session is `analyze` then `apply`.

```bash
util/backport/backport apply --open-pr
```

| Flag | Purpose |
| --- | --- |
| `--branch` | just this release branch |
| `--pr` | source pull request number, linked in each body and given a summary comment |
| `--remote` | fork remote the branches are pushed to, `origin` by default |
| `--dry-run` | print what would be pushed and opened, touch nothing |
| `--yes` | skip the confirm, for scripts and CI |

Branches go to your fork; the pull requests are opened against `aws/aws-lc`. Pushing
to `aws/aws-lc` is refused outright, so a stray `--remote` cannot put half-reviewed
work on the real repository.

`--dry-run` pushes nothing, opens nothing, and prints the summary comment instead of
posting it. The source pull request belongs to whoever wrote the fix, so a dry run does
not write to it either.

**Example Output:**

```
Fix ac3aee3104
Opening pull requests into aws/aws-lc for: fips-2025-09-12-lts, fips-2024-09-27
Branches are pushed to 'origin'
Go ahead? [Y/N] y
  fips-2025-09-12-lts: opened: https://github.com/aws/aws-lc/pull/3401
  fips-2024-09-27: unfinished: cherry-pick still open in .backport-worktrees/...

1 pull request(s) opened, 1 still need attention
  fips-2024-09-27
  Unfinished branches: resolve the conflict in the worktree, then
  'git cherry-pick --continue' there and run publish again.
```

**Results:**

| Result | Meaning |
| --- | --- |
| `opened` | pushed and a pull request created |
| `already open` | a pull request for that branch exists, so nothing was done again |
| `unfinished` | its cherry-pick is still stopped in the worktree, resolve it first |
| `missing` | no such backport branch, run `apply` first |
| `failed` | the push or the pull request failed, with the reason |

Nothing is ever a draft and nothing is auto-merged. Re-running is safe: a branch that
already has a pull request is left alone, and finishing a conflict by hand is enough
to let the next run pick it up, with no need to run `apply` again.

## Configuration

### Model settings

`.github/workflows/ai-config.json`, shared with the autofix workflow:

```json
{
  "aws_region": "us-west-2",
  "opus": "us.anthropic.claude-opus-5"
}
```

Both are required. The file also names the sonnet and haiku models that autofix uses,
which this tool ignores. To change the model, edit that file. Sharing it is what keeps
this tool and autofix from drifting onto different models.

The reply budget is `MAX_ANSWER_TOKENS` in `src/util/config.py`, next to the other
limits on what goes to the model. Keep it generous. The model thinks before answering,
and a small budget truncates the reply, which is treated as no answer and leaves those
branches flagged for review.

### How the model answers

It doesn't answer in prose. `consult_ai.py` sends one tool, `record_verdict`, and forces
it with `tool_choice`:

```json
{"affected": "yes" | "no" | "uncertain",
 "confidence": "high" | "medium" | "low",
 "reasoning": "2-4 sentences"}
```

Bedrock hands those back as a dict already shaped like the schema, so there is no reply
text to parse. That matters more than it sounds: every earlier version of this read the
verdict out of Markdown, and every bug in it was a parsing bug. A reasoning sentence that
happened to start with "No" could clear a branch.

`read_verdict` still validates what comes back rather than trusting it. Two Bedrock
limits are worth knowing:

- `"strict": true` on the tool is rejected for this model, so the enums are a strong
  steer and not a hard guarantee. A value outside them reads as no answer.
- `output_config` with a `json_schema` is rejected on this path too, which is why this
  uses forced tool use rather than the response-format style shown in the Bedrock guide.

Anything unreadable, a reply with no `record_verdict` call, or a reply cut short by the
token limit all count as no answer, and no answer leaves the branch flagged.

### Which branches count

Release branches are read from whichever remote points at `aws/aws-lc`, falling back to
`origin` when there is no such remote. `BACKPORT_REMOTE` overrides it.

That matters locally: `origin` is usually your own fork, which may not have the release
branches at all, or may be months behind on them. In CI there is only `origin` and it
already is `aws/aws-lc`, so the same rule picks the right thing in both places. Fetch
them first either way:

```bash
git fetch upstream
```

The branches found are then checked against `fips_versions.aws-lc.json`, which mirrors
the end-of-support table in `VERSIONING.md`. A branch past its end of support, or marked
as no longer actively maintained, is skipped and the reason is printed:

```
Skipping fips-2021-10-20: support ended 2026-10
```

It is printed rather than quietly left out, because a branch missing from the table and
a branch that never needed the fix look identical otherwise.

A branch that is **not** in the file is kept. Unknown must not mean silently skipped,
since the cost of that is a missed backport. A newly cut branch is analyzed from the day
it appears, and adding it to the file only matters once it has an end date.

When a branch ages out, update the file from `VERSIONING.md`. A unit test fails as soon
as anything listed in it is past its date, so this cannot rot unnoticed.

### Environment Variables

| Variable | Default | Purpose |
| --- | --- | --- |
| `BACKPORT_DISABLE_AI` | unset | set to `1` for the git-history pass only |
| `BACKPORT_REMOTE` | worked out | which remote the release branches are read from |
| `AWS_PROFILE` | unset | credentials for the AI pass. The region is not read from the environment |

## Project Structure

```
util/backport/
├── backport                      # entry point script
├── fips_versions.aws-lc.json     # which release branches are still in support
├── src/
│   ├── main.py                   # argument parsing
│   ├── commands/
│   │   ├── analyze.py            # the analyze command
│   │   ├── apply.py              # the apply command
│   │   └── publish.py            # the publish command
│   ├── engine/
│   │   ├── inspect_fix.py        # which lines the fix deletes, who wrote them
│   │   ├── discover_branches.py  # which release branches to check
│   │   ├── classify_branches.py  # already patched, then the verdict
│   │   ├── consult_ai.py         # the AI pass, and the verdict schema it answers with
│   │   └── prompts.py            # every word sent to the model
│   └── util/
│       ├── config.py             # verdicts, settings, the FIPS boundary, the saved run
│       ├── git.py                # everything that runs a git command
│       ├── github.py             # everything that talks to GitHub, through gh
│       └── render.py             # the output table and prompts
├── testing/
│   ├── test_engine.py            # unit tests, no repo or credentials
│   ├── replay_fixes.py           # replays real fixes and grades them
│   ├── fixes.txt                 # 39 real fixes to replay
│   └── answer_key.txt            # which branches each one should flag
└── .backport-runs/               # the last analyze result, not checked in
    .backport-worktrees/          # where a conflicted pick waits, not checked in
```

## Testing

### Unit tests

```bash
cd util/backport
python3 -m unittest testing.test_engine
```

Covers the pure helpers and the decision logic: the line filters, source file
selection, branch ordering, the verdict the model records and every way it can be
unreadable, the FIPS boundary check, the per-branch verdict table, and the guards that
stop an empty or truncated read from clearing a branch. No checkout or credentials
needed.

### Replay bench

```bash
cd util/backport
python3 testing/replay_fixes.py            # with the AI pass
python3 testing/replay_fixes.py --no-ai    # git history only
python3 testing/replay_fixes.py --fix 9545d9de6059
```

Replays 39 real AWS-LC fixes against checked answers. Each fix runs in a throwaway
sandbox wound back to just before it landed, so the tool cannot spot its own
backport. Objects are borrowed from your checkout, so nothing is cloned. A full run
takes about five minutes without the AI pass and roughly 20 minutes with it.

**Example Output:**

A block per fix, then the totals. One fix's block below, with the totals from a
full run:

```
=================================================================================
DH_check() excessive time with oversized modulus (CVE-2023-3446)
  fix 9545d9de6059  "Fix DH_check() excessive time with oversized modulus (#1109)"
=================================================================================
  changed files: ['crypto/dh_extra/dh_test.cc', 'crypto/fipsmodule/dh/check.c']
  bug commits:   ['95c29f3cd1']

  branch                   verdict    basis        answer key       result
  ------------------------ ---------- ------------ ---------------- ------
  fips-2022-11-02          affected   git history  affected/trailer OK
  fips-2021-10-20-1MU      affected   git history  affected/trailer OK
  fips-2021-10-20          affected   git history  affected/trailer OK

=================================================================================
157 branch cells over 39 fix(es)
=================================================================================
  correctly flagged     102
  correctly cleared     51
  unneeded flags        4
      real over-flags   0  history flagged it but the lines are absent, a tool error
      never shipped     2  lines still there, the flag is correct
      unclear           1  history could not tell, defaulted to affected
      AI upgraded       1  history unclear, the AI called it affected
      addition only     0  nothing deleted to look for
  MISSED BACKPORTS      0
  agreement             97%
```

Unneeded flags are split by cause, because only one kind is a tool error. There are
no real over-flags in either mode: git history never flags a branch whose lines are
provably absent. Of the 25 it leaves, 21 are branches it cannot settle, 2 are fixes
that only add lines so there is nothing to search for, and 2 are branches whose code
really is vulnerable but that were never given the fix.

| | git history only | with the AI pass |
| --- | --- | --- |
| unneeded flags | 25 | 4 |
| correctly cleared | 30 | 51 |
| missed backports | 0 | 0 |
| agreement | 84% | 97% |

The git-history column is exact and identical every run. The AI column is a single
sample taken on the model in `.github/workflows/ai-config.json`: the model does not give
the same answer every time, so expect a few unneeded flags either way.
Missed backports stay at 0 in both, because a branch the AI cannot clear stays
flagged.

**Missed backports must stay at 0.** That is the property worth protecting: an
unneeded flag costs a reviewer a few minutes, a missed one ships a vulnerability.
The bench exits non-zero if any appear.

Only branches that already existed when a fix landed are graded. A branch cut later
already carries the fix, so scoring it proves nothing.

## Troubleshooting

### No supported branches found

The release branches are not in your checkout, or they are on a remote the tool is not
reading. It reads whichever remote points at `aws/aws-lc`:

```bash
git remote -v
git fetch upstream
git branch -r | grep fips-
```

### Every branch comes back UNSURE

The AI could not be reached, so nothing resolved. The tool warns when this happens.
Check credentials and region:

```bash
export AWS_PROFILE=your-profile
aws sts get-caller-identity
```

A client is created even when credentials are expired, so a successful profile
listing is not proof. The warning after a run is.

### Nothing to analyze

The commit changes no files. A merge commit is the usual cause: it reports no changes
of its own, so analyze what it brought in instead.

```bash
util/backport/backport analyze --commit <sha>^..<sha>
```

### No saved analyze run

`apply` acts on what `analyze` decided, so `analyze` has to have run first:

```bash
util/backport/backport analyze
```

The same error appears if the run names a fix this checkout no longer has, which
happens when a range was analyzed and git has since collected the squashed commit.
Re-running `analyze` fixes both.

### No pull request can be opened

`publish` needs the GitHub CLI, installed and logged in:

```bash
gh auth login
gh auth status
```

In CI set `GH_TOKEN` instead, and give the job `contents: write` and
`pull-requests: write`.

### Refused to push to aws/aws-lc

Backport branches belong on a fork; only the pull requests go to `aws/aws-lc`. Point
`--remote` at your fork:

```bash
util/backport/backport publish --remote origin
```

### Wrong or empty results from a subdirectory

Should not happen. The tool pins itself to the checkout it lives in rather than
using your working directory. If you see empty results, file it as a bug.

## Support

- Every bench run prints the per-branch table and a note on every flag
- Check the `basis` column to see whether history or the AI decided a branch
- Contact the AWS-LC team
