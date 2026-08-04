#!/usr/bin/env python3
"""
Unit tests for the pure helpers, no repo or credentials needed
Everything repo-backed is covered by running analyze on a real fix

Run from util/backport:
    python3 -m unittest testing.test_engine
"""

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from engine import consult_ai, discover_branches, inspect_fix
from util import config


class NormalizeSpaces(unittest.TestCase):
    # Lines are compared after normalizing, so reindenting a file must not hide a
    # match. If this drifts, real vulnerable code stops being found.

    def test_collapses_and_strips(self):
        self.assertEqual(inspect_fix.normalize_spaces("  a   b\t c  "), "a b c")

    def test_whitespace_only(self):
        self.assertEqual(inspect_fix.normalize_spaces("   \t "), "")

    def test_newlines_collapse(self):
        # A whole file is normalized before a single line is searched for inside it,
        # so newlines have to become spaces or nothing ever matches
        self.assertEqual(inspect_fix.normalize_spaces("a\nb\r\nc"), "a b c")


class IsCFile(unittest.TestCase):
    # Decides whether # is a directive or a comment, which changes how every line
    # in a file is read.

    def test_c_family(self):
        for f in ("a.c", "a.cc", "a.CPP", "a.h", "a.hpp"):
            self.assertTrue(inspect_fix.is_c_file(f), f)

    def test_not_c(self):
        for f in ("a.py", "a.md", "a.S", None):
            self.assertFalse(inspect_fix.is_c_file(f), f)


class IsCommentOrBlank(unittest.TestCase):
    # Filters out lines that say nothing about the bug. Letting a comment through
    # is how a branch gets flagged for matching a stale comment.

    def test_blanks_and_comments(self):
        for s in ("", "   ", "// x", "/* x", "*/", "* x"):
            self.assertTrue(inspect_fix.is_comment_or_blank(s), repr(s))

    def test_punctuation_only(self):
        for s in ("}", "});", "{", ";"):
            self.assertTrue(inspect_fix.is_comment_or_blank(s), repr(s))

    def test_hash_is_code_in_c_but_comment_elsewhere(self):
        self.assertFalse(inspect_fix.is_comment_or_blank("#define X 1", "a.c"))
        self.assertTrue(inspect_fix.is_comment_or_blank("# a note", "a.py"))

    def test_real_code_kept(self):
        self.assertFalse(inspect_fix.is_comment_or_blank("if (ret <= 0) {", "a.c"))

    def test_goto_label_is_code(self):
        # The punctuation check must not swallow a label just because it ends in ':'
        self.assertFalse(inspect_fix.is_comment_or_blank("err:", "a.c"))

    def test_hash_without_a_filename_reads_as_a_comment(self):
        # With no filename the language is unknown. Calling it a comment drops the
        # line, which only weakens a match, so it is the safe direction
        self.assertTrue(inspect_fix.is_comment_or_blank("#define X 1"))


class IsTooCommonToMatch(unittest.TestCase):
    # Drops real code that appears everywhere. Skipping a line only weakens a
    # match, so being wrong here can never cause a missed backport.

    def test_bare_control_flow(self):
        for s in ("return 0;", "break;", "continue;", "goto err;"):
            self.assertTrue(inspect_fix.is_too_common_to_match(s), repr(s))

    def test_include(self):
        self.assertTrue(inspect_fix.is_too_common_to_match("#include <openssl/dh.h>"))

    def test_string_literal_only(self):
        self.assertTrue(inspect_fix.is_too_common_to_match('"DH_check"'))

    def test_distinctive_code_kept(self):
        self.assertFalse(
            inspect_fix.is_too_common_to_match("if (!BN_is_odd(dh->p)) return 0;")
        )

    def test_return_with_a_brace_is_kept(self):
        # The bare-return pattern stops at braces, so a compound return still counts
        self.assertFalse(inspect_fix.is_too_common_to_match("return (EC_GROUP){0};"))

    def test_empty(self):
        self.assertTrue(inspect_fix.is_too_common_to_match(""))


class OnlySourceFiles(unittest.TestCase):
    # A co-changed test or generated file must never decide a verdict, since
    # neither is the shipped code.

    def test_drops_tests_and_generated(self):
        files = ["crypto/x.c", "crypto/x_test.cc", "generated-src/a.S"]
        self.assertEqual(inspect_fix.only_source_files(files), ["crypto/x.c"])

    def test_keeps_everything_when_only_tests(self):
        files = ["crypto/x_test.cc"]
        self.assertEqual(inspect_fix.only_source_files(files), files)

    def test_keeps_everything_when_only_generated(self):
        files = ["generated-src/linux-x86/a.S"]
        self.assertEqual(inspect_fix.only_source_files(files), files)

    def test_empty(self):
        self.assertEqual(inspect_fix.only_source_files([]), [])


class IsTestOrGeneratedFile(unittest.TestCase):
    # The same check util.git and the engine share.

    def test_true_cases(self):
        for f in (
            "crypto/dh_extra/dh_test.cc",
            "generated-src/linux-x86/a.S",
            "test/foo.c",
            "crypto/test/bar.c",
            "fuzz/x.c",
        ):
            self.assertTrue(config.is_test_or_generated_file(f), f)

    def test_false_cases(self):
        for f in ("crypto/dh_extra/params.c", "ssl/tls13_both.cc", "include/x.h"):
            self.assertFalse(config.is_test_or_generated_file(f), f)

    def test_fuzz_matches_anywhere_in_the_path(self):
        # Deliberately a substring, not a directory check, so fuzzing helpers outside
        # fuzz/ are dropped too
        self.assertTrue(config.is_test_or_generated_file("ssl/test/fuzzer.h"))
        self.assertTrue(config.is_test_or_generated_file("crypto/bn/bn_to_fuzzer.go"))

    def test_empty_path(self):
        self.assertFalse(config.is_test_or_generated_file(""))

    def test_case_is_ignored(self):
        # Matches is_c_file, which also lowercases before checking
        self.assertTrue(config.is_test_or_generated_file("crypto/A_TEST.CC"))
        self.assertTrue(config.is_test_or_generated_file("TEST/foo.c"))


class FingerprintPathspec(unittest.TestCase):
    # Generated files are rebuilt per branch, so comparing them makes an identical
    # backport look like a different change.

    def test_excludes_generated(self):
        spec = config.fingerprint_pathspec()
        self.assertEqual(spec[:2], ["--", "."])
        self.assertIn(":(exclude)generated-src", spec)


class BranchOrder(unittest.TestCase):
    # Branch order drives the whole report, and an undated branch must not sort
    # above a real release.

    def test_date_key(self):
        self.assertEqual(
            discover_branches.branch_date_key("fips-2024-09-27"), "2024-09-27"
        )
        self.assertEqual(discover_branches.branch_date_key("NetOS"), "")

    def test_first_date_wins(self):
        self.assertEqual(
            discover_branches.branch_date_key("a-2020-01-01-b-2021-01-01"), "2020-01-01"
        )

    def test_empty(self):
        self.assertEqual(discover_branches.sort_branches([]), [])

    def test_newest_first_undated_last(self):
        names = ["fips-2021-10-20", "NetOS", "fips-2025-09-12-lts", "fips-2024-09-27"]
        self.assertEqual(
            discover_branches.sort_branches(names),
            ["fips-2025-09-12-lts", "fips-2024-09-27", "fips-2021-10-20", "NetOS"],
        )

    def test_same_date_ordered_by_name(self):
        names = ["fips-2021-10-20", "fips-2021-10-20-1MU"]
        self.assertEqual(
            discover_branches.sort_branches(names),
            ["fips-2021-10-20-1MU", "fips-2021-10-20"],
        )


class EmptyInputContracts(unittest.TestCase):
    # classify_branch reads these three as a tri-state, so the empty answers matter.
    # None means "nothing to look for", which is not the same as False, "looked and
    # it is gone". Confusing the two turns a branch that should be flagged for review
    # into a silent not affected. None of these reach git, so they run with no repo.

    def test_no_files_means_nothing_to_look_for(self):
        got = inspect_fix.buggy_lines_still_present("deadbeef", (), "origin/whatever")
        self.assertIsNone(got)

    def test_no_bug_commits_is_never_present(self):
        self.assertFalse(inspect_fix.any_bug_commit_present([], "origin/whatever"))

    def test_no_bug_commits_gives_an_empty_set(self):
        self.assertEqual(inspect_fix.bug_commits_present([], "whatever"), set())


class ReadAnswer(unittest.TestCase):
    # Turns the model's reply into a verdict. Misreading it either flips a branch
    # or throws away a good answer, and neither shows up as an error.

    def test_yes_and_no(self):
        yes = "**Likely affected**: Yes\n**Confidence**: high\n**Reasoning**: x"
        no = "**Likely affected**: No\n**Confidence**: medium\n**Reasoning**: x"
        self.assertEqual(consult_ai.read_answer(yes), (True, "high"))
        self.assertEqual(consult_ai.read_answer(no), (False, "medium"))

    def test_uncertain_has_no_verdict(self):
        raw = "**Likely affected**: Uncertain\n**Confidence**: low"
        self.assertEqual(consult_ai.read_answer(raw), (None, "low"))

    def test_missing_confidence_defaults_low(self):
        self.assertEqual(
            consult_ai.read_answer("**Likely affected**: Yes"), (True, "low")
        )

    def test_nothing_useful(self):
        # A truncated or off-format reply must not become a verdict
        for raw in ("", "I cannot help with that.", "### Reasoning\nsome prose"):
            self.assertEqual(consult_ai.read_answer(raw), (None, "low"), repr(raw))

    def test_case_and_spacing_ignored(self):
        raw = "- likely affected : yes\n- CONFIDENCE: High"
        self.assertEqual(consult_ai.read_answer(raw), (True, "high"))

    def test_both_labels_on_one_line(self):
        raw = "Likely affected: No, Confidence: high"
        self.assertEqual(consult_ai.read_answer(raw), (False, "high"))

    def test_confidence_without_a_verdict(self):
        self.assertEqual(
            consult_ai.read_answer("**Confidence**: medium"), (None, "medium")
        )

    def test_echoed_template_lands_on_affected(self):
        # If the model parrots the format line back, "yes" matches first and the
        # branch stays flagged. Wrong but safe, never a silent clear.
        raw = "- **Likely affected**: Yes / No / Uncertain"
        self.assertEqual(consult_ai.read_answer(raw)[0], True)


if __name__ == "__main__":
    unittest.main()
