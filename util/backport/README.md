# AWS-LC Backport Analysis

Works out which supported release branches still need a fix, before it merges.

## What This Tool Does

Given a fix on your branch (or any commit), `analyze` decides for every supported
FIPS release branch whether that branch still needs the fix. It does this in two
passes:

1. **Git history** - finds the distinctive lines the fix deletes, blames the commits
   that wrote them, and checks whether those commits and those lines reached each
   branch. This settles most branches on its own.
2. **AI** - only for branches history cannot settle, plus a second look at flagged
   branches that match just part of a fix's history. Advisory: it can add flags for
   a human to review, but a no-answer always leaves the branch flagged, so it can
   never hide a needed backport.

Nothing is cherry-picked, pushed, or committed. The tool only reports.

## Prerequisites

### Required Tools

- **Python 3**: for the tool itself, no third-party packages needed for the git pass
- **git**: with the release branches fetched (`git fetch origin`)
- **anthropic + boto3**: for the AI pass (`pip3 install --user anthropic boto3`)

### AWS Permissions

The AI pass calls Claude on Amazon Bedrock, so you need permission to invoke the
model named in `model-config.json`. Credentials are read through the normal AWS
chain (environment, `~/.aws`, SSO, IAM role).

## Setup

Run from the top of an AWS-LC checkout. The tool operates on the checkout it lives
in, so there is nothing to configure.

```bash
# make sure the release branches are present
git fetch origin

# set up credentials for the AI pass
export AWS_PROFILE=your-profile
export AWS_REGION=us-east-1
```

## Usage

### Analyze your current branch

```bash
util/backport/backport analyze
```

With no arguments this analyzes your branch's commits since `origin/main`. Several
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

## Configuration

### Model settings

`model-config.json` at the tool root:

```json
{
  "model_id": "us.anthropic.claude-opus-4-8",
  "aws_region": "us-west-2",
  "max_tokens": 4096
}
```

All three are required. To change the model, edit this file.

Keep `max_tokens` generous. The model thinks before answering, and a small budget
truncates the reply mid-answer, which shows up as every branch coming back
"uncertain".

### Environment Variables

| Variable | Default | Purpose |
| --- | --- | --- |
| `BACKPORT_DISABLE_AI` | unset | set to `1` for the git-history pass only |
| `BACKPORT_MAINLINE_REF` | `origin/main` | what release branches are compared against |
| `BACKPORT_BRANCH_PREFIXES` | `origin/fips-,origin/AWS-LC-FIPS-,origin/NetOS` | which branches count as releases |
| `BACKPORT_GENERATED_PATHS` | `generated-src` | machine-written paths to ignore |
| `AWS_PROFILE`, `AWS_REGION` | unset | credentials for the AI pass |

## Project Structure

```
util/backport/
├── backport                      # entry point script
├── model-config.json             # model id, region, token budget
├── src/
│   ├── main.py                   # argument parsing
│   ├── commands/
│   │   └── analyze.py            # the analyze command
│   ├── engine/
│   │   ├── inspect_fix.py        # which lines the fix deletes, who wrote them
│   │   ├── discover_branches.py  # which release branches to check
│   │   ├── classify_branches.py  # already patched, then the verdict
│   │   ├── consult_ai.py         # the AI pass
│   │   └── prompts.py            # every word sent to the model
│   └── util/
│       ├── config.py             # verdicts, settings, the saved run
│       ├── git.py                # everything that runs a git command
│       └── render.py             # the output table and prompts
├── testing/
│   ├── test_engine.py            # unit tests, no repo or credentials
│   ├── replay_fixes.py           # replays real fixes and grades them
│   ├── fixes.txt                 # 39 real fixes to replay
│   └── answer_key.txt            # which branches each one should flag
└── .backport-runs/               # the last analyze result, not checked in
```

## Testing

### Unit tests

```bash
cd util/backport
python3 -m unittest testing.test_engine
```

Covers the pure helpers: the line filters, source file selection, branch ordering,
and reading the model's reply. No checkout or credentials needed.

### Replay bench

```bash
cd util/backport
python3 testing/replay_fixes.py            # with the AI pass
python3 testing/replay_fixes.py --no-ai    # git history only
python3 testing/replay_fixes.py -v --fix 9545d9de6059
```

Replays 39 real AWS-LC fixes against checked answers. Each fix runs in a throwaway
sandbox wound back to just before it landed, so the tool cannot spot its own
backport. Objects are borrowed from your checkout, so nothing is cloned. A full run
takes about five minutes without the AI pass and roughly 20 minutes with it.

**Example Output:**

```
Replaying 39 fix(es), AI on

9545d9de6059  ok    TP=3 TN=0 FP=0 FN=0  DH_check() excessive time with oversized modul
2a184bd568ff  ok    TP=2 TN=3 FP=0 FN=0  ML-DSA constant-time hardening (#2602)

157 branch cells over 39 fix(es)
  correctly flagged     102
  correctly cleared     52
  unneeded flags        3
      real over-flags   0  history flagged it but the lines are absent, a tool error
      never shipped     2  lines still there, the flag is correct
      unclear           1  history could not tell, defaulted to affected
      AI upgraded       0  history unclear, the AI called it affected
      addition only     0  nothing deleted to look for
  MISSED BACKPORTS      0
  agreement             98%
```

Unneeded flags are split by cause, because only one kind is a tool error. There are
no real over-flags in either mode: git history never flags a branch whose lines are
provably absent. Of the 25 it leaves, 21 are branches it cannot settle, 2 are fixes
that only add lines so there is nothing to search for, and 2 are branches whose code
really is vulnerable but that were never given the fix.

| | git history only | with the AI pass |
| --- | --- | --- |
| unneeded flags | 25 | 3 |
| correctly cleared | 30 | 52 |
| missed backports | 0 | 0 |
| agreement | 84% | 98% |

The git-history column is exact and identical every run. The AI column is a single
sample: the model is not deterministic, so expect a few unneeded flags either way.
Missed backports stay at 0 in both, because a branch the AI cannot clear stays
flagged.

**Missed backports must stay at 0.** That is the property worth protecting: an
unneeded flag costs a reviewer a few minutes, a missed one ships a vulnerability.
The bench exits non-zero if any appear.

Only branches that already existed when a fix landed are graded. A branch cut later
already carries the fix, so scoring it proves nothing.

## Troubleshooting

### No supported branches found

The release branches are not in your checkout:

```bash
git fetch origin
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

### Every branch comes back "uncertain"

`max_tokens` in `model-config.json` is too small and replies are being cut off. The
tool prints a warning naming the branch when this happens. Raise it to 4096.

### Analysis is slow

The git pass takes a few seconds. Each AI call adds roughly 30 seconds, and only
unsettled branches trigger one. For a quick answer:

```bash
BACKPORT_DISABLE_AI=1 util/backport/backport analyze
```

### Wrong or empty results from a subdirectory

Should not happen. The tool pins itself to the checkout it lives in rather than
using your working directory. If you see empty results, file it as a bug.

## Support

- Re-run with `-v` on the bench to see per-branch reasoning
- Check the `basis` column to see whether history or the AI decided a branch
- Contact the AWS-LC team
