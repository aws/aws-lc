#!/usr/bin/env python3
"""
Unit tests for the publish <-> resolve plan hand-off.

`publish` attaches a machine-readable plan to the summary comment it posts on a PR: a
fenced ```json block carrying a `backport_bot_plan` sentinel key (publish.plan_marker).
`resolve` scrapes that plan back (resolve.parse_plan) so it can target exactly
the conflicting branches WITHOUT re-running the impact analysis.

These tests lock that contract end to end. It matters because the two sides live
in different modules and communicate only through the text of a PR comment: if the
marker format and the scraper ever drift apart, `resolve` silently falls back to a
full re-analysis (or, worse, targets the wrong branches) with no error. This file
is the regression net for that -- especially after the format moved from a hidden
HTML comment to the fenced-json block.

Run:
    python3 -m unittest testing.test_plan_roundtrip
"""

import sys
import unittest
from pathlib import Path

# The command modules live in src/commands, one directory up.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from commands import publish  # noqa: E402
from commands import resolve  # noqa: E402


def sample():
    """A representative run: one conflicting branch (with two files), one branch
    CI opened a clean PR for, and one not-affected branch."""
    fix = "ac3aee310abcdef"
    subject = "Recognise known safe DH groups"
    buckets = {
        "fips-2021-10-20": "affected",
        "fips-2024-09-27": "affected",
        "main": "not_affected",
    }
    outcomes = {
        "fips-2021-10-20": (
            "conflict",
            [{"path": "crypto/dh/dh.c"}, {"path": "tls/t.c"}],
        ),
        "fips-2024-09-27": ("opened", "https://github.com/x/y/pull/99"),
    }
    return fix, subject, buckets, outcomes


class PlanRoundTrip(unittest.TestCase):
    def test_full_summary_comment_roundtrips(self):
        # Catches: the plan not surviving inside a REAL summary comment. The comment
        # `publish` posts also contains a ```bash `backport resolve` block and a markdown
        # table -- the scraper must still pull the fix SHA and conflict targets back
        # out intact. If this breaks, resolve can't recover what publish decided.
        fix, subject, buckets, outcomes = sample()
        comment = (
            publish.summary_table(fix, subject, buckets, outcomes, source_pr=59)
            + "\n\n"
            + publish.plan_marker(fix, subject, buckets, outcomes)
        )
        plan = resolve.parse_plan(comment)
        self.assertIsNotNone(plan, "plan not found in the summary comment")
        self.assertEqual(plan["fix"], fix)
        targets = [
            b for b, i in plan["branches"].items() if i.get("outcome") == "conflict"
        ]
        self.assertEqual(targets, ["fips-2021-10-20"])

    def test_conflict_file_list_is_preserved(self):
        # Catches: the per-branch conflict file list being dropped or reshaped.
        # resolve shows these paths to the user ("Conflicting files:"), so losing
        # them degrades the whole point of reading the plan.
        fix, subject, buckets, outcomes = sample()
        plan = resolve.parse_plan(publish.plan_marker(fix, subject, buckets, outcomes))
        self.assertEqual(
            plan["branches"]["fips-2021-10-20"]["files"],
            ["crypto/dh/dh.c", "tls/t.c"],
        )

    def test_bash_command_block_is_not_mistaken_for_the_plan(self):
        # Catches: the scraper grabbing some other fenced block. The summary's
        # ```bash command block has no sentinel key, so parse_plan must skip it
        # and only accept the sentinel-bearing json block.
        fix, subject, buckets, outcomes = sample()
        comment = publish.summary_table(fix, subject, buckets, outcomes, source_pr=59)
        # The table alone (with its ```bash block) carries NO plan -> None.
        self.assertIsNone(resolve.parse_plan(comment))

    def test_latest_plan_wins(self):
        # Catches: picking a stale plan when a PR has several. publish posts one, then a
        # resolve run posts an updated summary; the reader must take the NEWEST,
        # else it would try to re-open branches already resolved.
        fix, subject, buckets, outcomes = sample()
        old = publish.plan_marker("oldsha0000000", subject, buckets, outcomes)
        # Newer run: the previously-conflicting branch is now opened.
        new_outcomes = dict(outcomes)
        new_outcomes["fips-2021-10-20"] = ("done", "https://github.com/x/y/pull/101")
        new = publish.plan_marker("newsha1111111", subject, buckets, new_outcomes)
        plan = resolve.parse_plan(old + "\n\n---\n\n" + new)
        self.assertEqual(plan["fix"], "newsha1111111")
        self.assertEqual(plan["branches"]["fips-2021-10-20"]["outcome"], "done")

    def test_no_plan_returns_none(self):
        # Catches: a plain PR (no bot comment) not returning None. None is the
        # signal that tells resolve to fall back to a local re-analysis, so it must
        # be unambiguous.
        self.assertIsNone(resolve.parse_plan("just a normal PR comment, no plan"))

    def test_malformed_json_block_is_ignored(self):
        # Catches: a broken/half-written json block crashing the scraper instead of
        # being skipped. A truncated comment must not take down `resolve`.
        broken = "```json\n{ not valid json,, }\n```"
        self.assertIsNone(resolve.parse_plan(broken))


if __name__ == "__main__":
    unittest.main(verbosity=2)
