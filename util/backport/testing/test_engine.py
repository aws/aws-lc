#!/usr/bin/env python3
"""
Unit tests for the pure (repo-independent) helpers in engine/analysis.py.

These run without an aws-lc checkout, credentials, or network -- they only
exercise the string/date logic the impact analyzer relies on. For the
end-to-end, repo-backed behavior see replay_real_cve.py (real replays).

Each test says what it is trying to catch and why that matters: most of these
helpers exist to keep the impact engine from over-flagging (matching stale
comments / boilerplate) or from crashing on messy input, so a regression here
shows up as noisy or wrong branch verdicts downstream.

Run:
    python3 -m unittest testing.test_engine        # from the util/backport dir
    python3 testing/test_engine.py                 # or directly
"""

import sys
import unittest
from datetime import date
from pathlib import Path

# The tool's packages live in the src/ folder one directory up.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from engine import analysis as engine  # noqa: E402


class NormWhitespace(unittest.TestCase):
    # normalize_spaces canonicalizes whitespace before we compare a fix's
    # removed lines against a branch. If it drifted, a line that only differs by
    # reindentation/tabs would look "changed" and the vulnerable-code check would
    # give the wrong answer.

    def test_collapses_runs_and_strips(self):
        # Catches: runs of mixed spaces/tabs not collapsing to a single space, or
        # leading/trailing whitespace not being stripped.
        self.assertEqual(engine.normalize_spaces("  a   b\t c  "), "a b c")

    def test_empty(self):
        # Catches: whitespace-only input not normalizing to "" (it must, so a
        # blank line never accidentally matches real content).
        self.assertEqual(engine.normalize_spaces("   \t "), "")


class IsCFile(unittest.TestCase):
    # is_c_file decides which files get C-aware line handling (e.g. treating '#'
    # as a preprocessor directive, not a comment). A misclassification flips that
    # behavior for a whole file.

    def test_c_family(self):
        # Catches: any C/C++ source or header extension being missed.
        for f in ("a.c", "b.cc", "d.h", "e.hpp", "f.cxx"):
            self.assertTrue(engine.is_c_file(f), f)

    def test_non_c(self):
        # Catches: non-C files (build/scripts/config) or None being wrongly
        # treated as C -- which would misread '#' lines as code.
        for f in ("CMakeLists.txt", "x.py", "y.pl", "z.S", "build.yaml", None):
            self.assertFalse(engine.is_c_file(f), f)


class IsNoiseLine(unittest.TestCase):
    # is_comment_or_blank filters lines that carry no distinctive code, so bug commit
    # tracing and the line matching don't latch onto them. If real code slipped
    # through as "noise" we'd miss a hit; if noise slipped through as code, a
    # stale comment could trace to an ancient import and over-flag the branch.

    def test_blank_and_comments(self):
        # Catches: blank lines and C comment forms not being recognized as noise.
        for s in ("", "   ", "// comment", "/* block", "* doc", "*/"):
            self.assertTrue(engine.is_comment_or_blank(s), repr(s))

    def test_punctuation_only(self):
        # Catches: lone braces/semicolons counting as meaningful code (they're on
        # nearly every branch, so they'd match everything).
        for s in ("{", "}", "});", "  ;  "):
            self.assertTrue(engine.is_comment_or_blank(s), repr(s))

    def test_hash_is_comment_in_non_c_but_code_in_c(self):
        # Catches: the language-sensitive '#' rule regressing. '#' is a comment in
        # scripts/CMake/YAML ...
        self.assertTrue(
            engine.is_comment_or_blank("# a cmake comment", "CMakeLists.txt")
        )
        # ... but a preprocessor directive (real code) in C/C++, so it must NOT be
        # dropped as noise there.
        self.assertFalse(engine.is_comment_or_blank("#include <foo.h>", "a.c"))
        self.assertFalse(engine.is_comment_or_blank("#if defined(X)", "b.h"))

    def test_real_code_is_not_noise(self):
        # Catches: an over-eager filter discarding a genuine statement, which would
        # cause a real vulnerable line to be ignored (a silent miss).
        self.assertFalse(
            engine.is_comment_or_blank("int rc = do_thing(ptr, len);", "a.c")
        )


class IsBoilerplateLine(unittest.TestCase):
    # is_too_common_to_match drops lines that are real code but too generic to
    # identify a specific fix (they recur across unrelated files/branches).
    # Keeping them would make lines match by coincidence and over-flag.

    def test_bare_control_flow(self):
        # Catches: ubiquitous control-flow statements being treated as distinctive.
        for s in ("return;", "break;", "continue;", "goto err;", "return 0;"):
            self.assertTrue(engine.is_too_common_to_match(s), repr(s))

    def test_include(self):
        # Catches: an #include (present in countless files) counting as a
        # fingerprint of the fix.
        self.assertTrue(engine.is_too_common_to_match('#include "internal.h"'))

    def test_string_literal_only(self):
        # Catches: a bare string literal being treated as distinctive code.
        self.assertTrue(engine.is_too_common_to_match('"SHA2-512"'))

    def test_distinctive_code_is_kept(self):
        # Catches: the filter over-reaching and discarding a line that IS specific
        # to the fix -- that would weaken the match and risk a miss.
        self.assertFalse(
            engine.is_too_common_to_match("if (EVP_MD_size(md) <= 0) return 0;")
        )


class ParseEosDate(unittest.TestCase):
    # parse_support_end_date reads end-of-support dates from the FIPS manifest to apply
    # the support-window filter. It must accept the published formats and return
    # None (never raise) on anything unexpected, or a bad manifest entry would
    # crash branch resolution.

    def test_full_date(self):
        # Catches: the normal YYYY-MM-DD form not parsing.
        self.assertEqual(engine.parse_support_end_date("2025-09-12"), date(2025, 9, 12))

    def test_year_month(self):
        # Catches: the month-precision YYYY-MM form (as VERSIONING.md publishes it)
        # not being accepted; the day must default to the 1st.
        self.assertEqual(engine.parse_support_end_date("2025-09"), date(2025, 9, 1))

    def test_invalid(self):
        # Catches: malformed/None/foreign-format values raising instead of
        # returning None (which the caller treats as "no known EOS date").
        for bad in (None, "", "not-a-date", "2025/09/12"):
            self.assertIsNone(engine.parse_support_end_date(bad), repr(bad))


class PatchIdPathspec(unittest.TestCase):
    # fingerprint_pathspec builds the git pathspec that excludes generated files
    # from fingerprint matching. The contract the callers rely on is only that it
    # always yields a list of git args and never raises.

    def test_returns_list(self):
        # Catches: it returning a non-list or throwing (which would break every
        # already-patched / fingerprint comparison).
        self.assertIsInstance(engine.fingerprint_pathspec(), list)


if __name__ == "__main__":
    unittest.main(verbosity=2)
