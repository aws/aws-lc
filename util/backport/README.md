# AWS-LC Backport Bot

Decides which supported AWS-LC release branches a fix belongs on, then backports it.
Point it at your fix -- a commit, a range of commits, or just your current branch --
and it gives every supported FIPS release branch a verdict (AFFECTED / not affected /
already patched), cherry-picks onto local branches, and walks you through any
conflicts. Nothing is ever auto-merged, and it never targets upstream `aws/aws-lc`.

## Prerequisites

Run from an AWS-LC checkout with the release branches fetched (`git fetch origin`).
Python 3.9+. The optional AI layer needs `anthropic` + `boto3`
(`pip install -r requirements.txt`) and AWS credentials; without them the
deterministic engine runs alone.

## Commands

```bash
cd <aws-lc>

# 1. Which branches need this fix?
#    Omit --commit to use your branch's commits since origin/main.
util/backport/backport analyze --commit <sha>

# 2. Cherry-pick onto local backport/<branch>/<id> branches (nothing is pushed)
util/backport/backport apply --all-affected

# 3. Resolve any conflicts interactively, then open one PR per branch
util/backport/backport resolve --pr <number>

# Post-merge automation (what CI runs): one backport PR per affected branch
util/backport/backport publish --commit <merged-sha> --pr <number>

# Drop the saved run state
util/backport/backport clear
```

Useful flags: `--no-ai` (deterministic only), `--branches <a b c>` (limit the set),
`--json` (machine-readable), `--repo <path>` (target another checkout),
`--commit A..B` (a fix spread across several commits, analyzed as its net change),
`--dry-run` (`publish` only).

`apply` and `resolve` check each release branch out in your own working tree (so
your IDE shows the conflict live) and put you back on your original branch when
they are done, so they need a clean tree to start.

## How it decides

Per fix × branch, deterministically first; the AI is consulted only when git history
is inconclusive:

1. Fix already in the branch's history (ancestry / patch-id) → **already patched**.
2. The exact lines the fix removes are still present → **AFFECTED**.
3. Provably gone but the file is still there → ask the AI.
4. Code genuinely absent → **not affected**.

The bias is deliberate: anything ambiguous becomes AFFECTED for review, so the tool
may over-flag but never silently drops a needed backport.

## Configuration

`model-config.json` holds the Bedrock model pin and call limits. Environment
overrides: `BACKPORT_REPO_PATH`, `BEDROCK_MODEL_ID`, `AWS_REGION`,
`BACKPORT_DISABLE_AI=1`, `BACKPORT_GENERATED_PATHS`, `BACKPORT_MAINLINE_REF`,
`BACKPORT_BRANCH_PREFIXES`, `BACKPORT_VERSIONS_MANIFEST`.

## Tests

```bash
cd util/backport
python3 -m unittest discover -s testing -p 'test_*.py'   # 22 unit tests; no repo/creds needed
```

`testing/replay_real_cve.py` replays real CVE fixes in a throwaway sandbox (the real
repo is only ever read) and grades `verdicts`' shipped classifier against
`testing/answer_key.txt` — 31 fixes / 186 fix-branch cells. Deterministic-only
(`--no-ai`): **0 false negatives**, at a 23.7% over-flag rate (44/186 cells flagged
for review that did not need a backport). Cutting those down is what the AI
advisory layer is for. See `testing/reliable_cves.txt` for how to run it.

To wire up the post-merge bot, copy `backport-bot.yml` into `.github/workflows/`.
