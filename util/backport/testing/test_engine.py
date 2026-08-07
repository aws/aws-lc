#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
"""
Unit tests for the pure helpers, no repo or credentials needed
Everything repo-backed is covered by running analyze on a real fix

Run from util/backport:
    python3 -m unittest testing.test_engine
"""

import subprocess
import sys
import unittest
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from engine import classify_branches, consult_ai, discover_branches, inspect_fix
from util import config, git


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
        raw = "- **Likely affected**: Yes | No | Uncertain"
        self.assertEqual(consult_ai.read_answer(raw)[0], True)

    def test_off_menu_answers_never_clear_a_branch(self):
        # "no" is a substring of unknown, cannot, not and none. Reading any of them
        # as a no would clear a branch the model was telling us it could not judge,
        # which is the one failure that ships a vulnerability. A hedge that opens on
        # the word itself, like "No idea", still reads as a no, so the prompt asks
        # for one of the three words and nothing else
        for answer in (
            "Unknown",
            "Cannot determine",
            "Not enough information",
            "None",
            "Indeterminate",
            "Not applicable",
        ):
            got = consult_ai.read_answer(f"**Likely affected**: {answer}")[0]
            self.assertIsNone(got, f"{answer!r} parsed as {got!r}, must be None")

    def test_exact_yes_and_no_still_parse(self):
        self.assertIs(consult_ai.read_answer("**Likely affected**: No")[0], False)
        self.assertIs(consult_ai.read_answer("**Likely affected**: Yes")[0], True)
        self.assertIsNone(consult_ai.read_answer("**Likely affected**: Uncertain")[0])

    def test_confidence_matches_whole_words(self):
        # A level has to stand on its own, so "highest" leaves the default in place
        self.assertEqual(consult_ai.read_answer("**Confidence**: highest")[1], "low")
        self.assertEqual(consult_ai.read_answer("**Confidence**: high")[1], "high")


# _________ Test Doubles For The Verdict Layer _________

# Stand-in names for one fix and one release branch. classify_branches only ever
# hands these to git, so faking git out means none of it has to be real.
FIX_SHA = "deadbeef"
BUG_COMMITS = ["cafe1234"]
BRANCH = "fips-2024-09-27"
REF = "origin/fips-2024-09-27"
SRC_FILES = ["crypto/fipsmodule/bn/bn.c"]


def completed(returncode: int = 0, stdout: Any = "") -> subprocess.CompletedProcess:
    """What git_in_repo hands back, without running git"""
    return subprocess.CompletedProcess(
        args=["git"], returncode=returncode, stdout=stdout
    )


class FakeGit:
    """
    Stands in for git_in_repo, answering each subcommand from a table
    An unstubbed command raises, so a test cannot lean on one it never thought about
    """

    def __init__(self, answers: Dict[str, Any]) -> None:
        self.answers = answers
        self.commands: List[List[str]] = []
        self.inputs: List[Any] = []

    def __call__(self, args: Sequence[str], **kwargs: Any) -> Any:
        command = list(args)
        self.commands.append(command)
        self.inputs.append(kwargs.get("input"))
        if command[0] not in self.answers:
            raise AssertionError(f"unstubbed git command: {command}")
        return self.answers[command[0]]

    def subcommands(self) -> List[str]:
        """The git subcommand from each call, in order"""
        return [command[0] for command in self.commands]


def fake_patched_lookups(
    ancestor: bool,
    mentions: bool = False,
    fingerprint: Optional[str] = None,
    on_branch: Sequence[str] = (),
) -> Any:
    """Fakes the three ways is_already_patched can find the fix on a branch"""
    return mock.patch.multiple(
        classify_branches,
        git_in_repo=FakeGit({"merge-base": completed(returncode=0 if ancestor else 1)}),
        branch_mentions_cherry_pick=lambda commit, ref: mentions,
        change_fingerprint=lambda commit: fingerprint,
        branch_fingerprints=lambda ref: set(on_branch),
    )


def fake_branch_files(
    by_name: Dict[str, List[str]],
    removed: Dict[str, List[str]],
    contents: Dict[str, str],
) -> Any:
    """Fakes the branch's file list, the fix's deleted lines, and file contents"""
    return mock.patch.multiple(
        classify_branches,
        branch_paths_by_basename=lambda ref: by_name,
        deleted_lines=lambda sha, file: removed.get(file, []),
        show_file=lambda ref, path: contents.get(path),
    )


def fake_verdict_inputs(
    already: bool = False,
    affected: bool = False,
    still_present: Optional[bool] = None,
    on_branch: bool = False,
    same_named: bool = False,
) -> Any:
    """Fakes every lookup classify_branch makes, so only the decision is tested"""
    return mock.patch.multiple(
        classify_branches,
        is_already_patched=lambda sha, branch: already,
        any_bug_commit_present=lambda commits, ref: affected,
        buggy_lines_still_present=lambda sha, files, ref: still_present,
        get_file_on_branch=lambda file, ref, commit=None: (
            ("code", file) if on_branch else (None, None)
        ),
        same_named_file_carries_fix=lambda sha, files, ref: same_named,
    )


def never_called(*args: Any, **kwargs: Any) -> Any:
    """A double for a step a test expects to be skipped"""
    raise AssertionError(f"a step that should have been skipped ran with {args}")


class ChangeFingerprint(unittest.TestCase):
    # A patch-id is how the same fix under a different SHA is recognized. Getting one
    # wrong either hides a backport that is already there or invents one that is not.

    def test_the_first_token_of_patch_id_is_the_fingerprint(self):
        # patch-id prints "<patch id> <commit sha>", and only the first is the content
        fake = FakeGit(
            {
                "show": completed(stdout=b"diff --git a/x.c b/x.c\n"),
                "patch-id": completed(stdout=b"aaa111 bbb222\n"),
            }
        )
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            self.assertEqual(classify_branches.change_fingerprint(FIX_SHA), "aaa111")

    def test_the_commit_diff_is_piped_into_patch_id(self):
        # patch-id reads the diff on stdin, so a lost pipe would fingerprint nothing
        fake = FakeGit(
            {
                "show": completed(stdout=b"diff --git a/x.c b/x.c\n"),
                "patch-id": completed(stdout=b"aaa111\n"),
            }
        )
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            classify_branches.change_fingerprint(FIX_SHA)
        self.assertIn(b"diff --git a/x.c b/x.c\n", fake.inputs)

    def test_generated_files_are_left_out_of_the_fingerprint(self):
        # Each branch rebuilds generated-src itself, so including it would make an
        # identical backport look like a different change
        fake = FakeGit(
            {
                "show": completed(stdout=b"a diff"),
                "patch-id": completed(stdout=b"aaa111\n"),
            }
        )
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            classify_branches.change_fingerprint(FIX_SHA)
        self.assertIn(":(exclude)generated-src", fake.commands[0])

    def test_a_commit_git_cannot_show_has_no_fingerprint(self):
        fake = FakeGit({"show": completed(returncode=128, stdout=b"")})
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            self.assertIsNone(classify_branches.change_fingerprint("nosuchcommit"))
        # Nothing to hash, so patch-id is never reached
        self.assertEqual(fake.subcommands(), ["show"])

    def test_a_failed_patch_id_has_no_fingerprint(self):
        fake = FakeGit(
            {
                "show": completed(stdout=b"a diff"),
                "patch-id": completed(returncode=1, stdout=b""),
            }
        )
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            self.assertIsNone(classify_branches.change_fingerprint(FIX_SHA))

    def test_an_empty_patch_id_has_no_fingerprint(self):
        # An empty commit hashes to nothing. Returning "" would then match the next
        # empty one and read as already patched
        fake = FakeGit(
            {
                "show": completed(stdout=b""),
                "patch-id": completed(stdout=b"  \n"),
            }
        )
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            self.assertIsNone(classify_branches.change_fingerprint(FIX_SHA))


class BranchFingerprints(unittest.TestCase):
    # The set the fix's own fingerprint is looked up in. Coming back empty on an error
    # only costs the already-patched shortcut, so it can never miss a backport.

    def test_one_fingerprint_per_branch_commit(self):
        fake = FakeGit(
            {
                "log": completed(stdout=b"a log with patches"),
                "patch-id": completed(stdout=b"aaa111 ccc\nbbb222 ddd\n"),
            }
        )
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            got = classify_branches.branch_fingerprints(REF)
        self.assertEqual(got, {"aaa111", "bbb222"})

    def test_blank_lines_are_skipped(self):
        fake = FakeGit(
            {
                "log": completed(stdout=b"a log"),
                "patch-id": completed(stdout=b"aaa111 ccc\n\n   \nbbb222 ddd\n"),
            }
        )
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            got = classify_branches.branch_fingerprints(REF)
        self.assertEqual(got, {"aaa111", "bbb222"})

    def test_only_commits_mainline_does_not_have_are_read(self):
        # A fingerprint shared with mainline says nothing about a backport, and the
        # range is the only thing keeping those out
        fake = FakeGit(
            {
                "log": completed(stdout=b"a log"),
                "patch-id": completed(stdout=b"aaa111\n"),
            }
        )
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            classify_branches.branch_fingerprints(REF)
        self.assertIn(f"{config.MAINLINE_REF}..{REF}", fake.commands[0])

    def test_a_failed_log_gives_an_empty_set(self):
        fake = FakeGit({"log": completed(returncode=128, stdout=b"")})
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            self.assertEqual(
                classify_branches.branch_fingerprints("origin/gone"), set()
            )

    def test_a_failed_patch_id_gives_an_empty_set(self):
        fake = FakeGit(
            {
                "log": completed(stdout=b"a log"),
                "patch-id": completed(returncode=1, stdout=b""),
            }
        )
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            self.assertEqual(classify_branches.branch_fingerprints(REF), set())


class BranchMentionsCherryPick(unittest.TestCase):
    # Catches a backport that was reshaped on the way over, so its contents no longer
    # fingerprint the same. Missing one only sends a patched branch back for review.

    def test_a_trailer_naming_the_fix_counts_as_a_mention(self):
        full = "a" * 40
        fake = FakeGit(
            {
                "rev-parse": completed(stdout=full + "\n"),
                "log": completed(
                    stdout=f"fix a thing\n\n(cherry picked from commit {full})\n\x00"
                ),
            }
        )
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            self.assertTrue(classify_branches.branch_mentions_cherry_pick(full, REF))

    def test_a_ref_is_resolved_to_its_sha_before_the_search(self):
        # The trailer holds a full SHA, so a name like HEAD has to be resolved first
        # or the text could never match
        full = "a" * 40
        fake = FakeGit(
            {
                "rev-parse": completed(stdout=full + "\n"),
                "log": completed(stdout=f"(cherry picked from commit {full})\n"),
            }
        )
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            self.assertTrue(classify_branches.branch_mentions_cherry_pick("HEAD", REF))

    def test_another_commits_trailer_is_not_a_mention(self):
        fake = FakeGit(
            {
                "rev-parse": completed(stdout="a" * 40 + "\n"),
                "log": completed(
                    stdout="(cherry picked from commit " + "b" * 40 + ")\n"
                ),
            }
        )
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            self.assertFalse(
                classify_branches.branch_mentions_cherry_pick("a" * 40, REF)
            )

    def test_a_commit_this_checkout_does_not_have_is_not_a_mention(self):
        fake = FakeGit({"rev-parse": completed(returncode=1, stdout="")})
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            self.assertFalse(
                classify_branches.branch_mentions_cherry_pick("nosuchcommit", REF)
            )
        # No SHA to search for, so the branch log is never read
        self.assertEqual(fake.subcommands(), ["rev-parse"])

    def test_an_empty_rev_parse_is_not_a_mention(self):
        # --quiet makes rev-parse exit 0 with no output for some bad names, so the
        # returncode alone is not enough to trust
        fake = FakeGit({"rev-parse": completed(stdout="\n")})
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            self.assertFalse(classify_branches.branch_mentions_cherry_pick("", REF))
        self.assertEqual(fake.subcommands(), ["rev-parse"])

    def test_a_failed_log_is_not_a_mention(self):
        fake = FakeGit(
            {
                "rev-parse": completed(stdout="a" * 40 + "\n"),
                "log": completed(returncode=128, stdout=""),
            }
        )
        with mock.patch.object(classify_branches, "git_in_repo", fake):
            self.assertFalse(
                classify_branches.branch_mentions_cherry_pick("a" * 40, "origin/gone")
            )


class IsAlreadyPatched(unittest.TestCase):
    # Runs before the verdict and outranks it, so a false yes here silently drops a
    # branch that still needs the fix.

    def test_shared_history_counts_as_patched(self):
        with fake_patched_lookups(ancestor=True):
            self.assertTrue(classify_branches.is_already_patched(FIX_SHA, BRANCH))

    def test_a_cherry_pick_trailer_counts_as_patched(self):
        with fake_patched_lookups(ancestor=False, mentions=True):
            self.assertTrue(classify_branches.is_already_patched(FIX_SHA, BRANCH))

    def test_the_same_change_under_another_sha_counts_as_patched(self):
        with fake_patched_lookups(
            ancestor=False, fingerprint="aaa111", on_branch=["aaa111", "bbb222"]
        ):
            self.assertTrue(classify_branches.is_already_patched(FIX_SHA, BRANCH))

    def test_a_branch_with_none_of_the_three_signs_is_not_patched(self):
        with fake_patched_lookups(
            ancestor=False, fingerprint="aaa111", on_branch=["bbb222"]
        ):
            self.assertFalse(classify_branches.is_already_patched(FIX_SHA, BRANCH))

    def test_a_fingerprint_that_could_not_be_computed_never_matches(self):
        with fake_patched_lookups(
            ancestor=False, fingerprint=None, on_branch=["aaa111"]
        ):
            self.assertFalse(classify_branches.is_already_patched(FIX_SHA, BRANCH))

    def test_an_empty_fingerprint_never_matches_an_empty_one(self):
        # Two things that hashed to nothing are not the same change
        with fake_patched_lookups(ancestor=False, fingerprint="", on_branch=[""]):
            self.assertFalse(classify_branches.is_already_patched(FIX_SHA, BRANCH))

    def test_shared_history_stops_before_the_expensive_checks(self):
        # Fingerprinting a branch walks its whole log, so the cheap ancestor test has
        # to answer on its own
        with mock.patch.multiple(
            classify_branches,
            git_in_repo=FakeGit({"merge-base": completed()}),
            branch_mentions_cherry_pick=never_called,
            change_fingerprint=never_called,
            branch_fingerprints=never_called,
        ):
            self.assertTrue(classify_branches.is_already_patched(FIX_SHA, BRANCH))

    def test_the_branch_name_is_read_as_an_origin_ref(self):
        # Branches are named bare everywhere else in the tool, and a local name would
        # quietly resolve to something else or nothing
        fake = FakeGit({"merge-base": completed(returncode=1)})
        with mock.patch.multiple(
            classify_branches,
            git_in_repo=fake,
            branch_mentions_cherry_pick=lambda commit, ref: False,
            change_fingerprint=lambda commit: None,
        ):
            classify_branches.is_already_patched(FIX_SHA, BRANCH)
        self.assertIn(REF, fake.commands[0])


class SameNamedFileCarriesFix(unittest.TestCase):
    # The last look before a branch is called not affected. It has to find a file that
    # moved somewhere git could not follow, without accepting one that shares a name.

    def test_a_moved_file_holding_a_deleted_line_is_a_hit(self):
        with fake_branch_files(
            by_name={"bn.c": ["crypto/bn/bn.c"]},
            removed={SRC_FILES[0]: ["if (!BN_is_odd(dh->p))"]},
            contents={"crypto/bn/bn.c": "int f() {\n  if (!BN_is_odd(dh->p))\n}\n"},
        ):
            self.assertTrue(
                classify_branches.same_named_file_carries_fix(FIX_SHA, SRC_FILES, REF)
            )

    def test_a_shared_name_alone_is_not_enough(self):
        # A name proves nothing, so a fix that deletes no distinctive line cannot
        # flag a branch, and the file is never even read
        with mock.patch.multiple(
            classify_branches,
            branch_paths_by_basename=lambda ref: {"bn.c": ["crypto/bn/bn.c"]},
            deleted_lines=lambda sha, file: [],
            show_file=never_called,
        ):
            self.assertFalse(
                classify_branches.same_named_file_carries_fix(FIX_SHA, SRC_FILES, REF)
            )

    def test_no_file_of_that_name_on_the_branch_is_not_a_hit(self):
        with fake_branch_files(
            by_name={"other.c": ["crypto/other.c"]},
            removed={SRC_FILES[0]: ["if (!BN_is_odd(dh->p))"]},
            contents={},
        ):
            self.assertFalse(
                classify_branches.same_named_file_carries_fix(FIX_SHA, SRC_FILES, REF)
            )

    def test_a_file_that_cannot_be_read_is_not_a_hit(self):
        with fake_branch_files(
            by_name={"bn.c": ["crypto/bn/bn.c"]},
            removed={SRC_FILES[0]: ["if (!BN_is_odd(dh->p))"]},
            contents={},
        ):
            self.assertFalse(
                classify_branches.same_named_file_carries_fix(FIX_SHA, SRC_FILES, REF)
            )

    def test_a_same_named_file_without_the_bug_is_not_a_hit(self):
        with fake_branch_files(
            by_name={"bn.c": ["crypto/bn/bn.c"]},
            removed={SRC_FILES[0]: ["if (!BN_is_odd(dh->p))"]},
            contents={"crypto/bn/bn.c": "int f() {\n  return 1;\n}\n"},
        ):
            self.assertFalse(
                classify_branches.same_named_file_carries_fix(FIX_SHA, SRC_FILES, REF)
            )

    def test_reindented_code_still_matches(self):
        # An old branch often carries the same logic under different formatting, and
        # both sides are normalized so it still counts
        with fake_branch_files(
            by_name={"bn.c": ["crypto/bn/bn.c"]},
            removed={SRC_FILES[0]: ["if (!BN_is_odd(dh->p))  {"]},
            contents={"crypto/bn/bn.c": "\tif   (!BN_is_odd(dh->p))\t{\n"},
        ):
            self.assertTrue(
                classify_branches.same_named_file_carries_fix(FIX_SHA, SRC_FILES, REF)
            )

    def test_every_path_with_that_name_is_checked(self):
        # internal.h shows up dozens of times, so the search cannot stop at the first
        with fake_branch_files(
            by_name={"internal.h": ["ssl/internal.h", "crypto/bn/internal.h"]},
            removed={
                "crypto/fipsmodule/bn/internal.h": ["void bn_mul_mont_small(void)"]
            },
            contents={
                "ssl/internal.h": "something else\n",
                "crypto/bn/internal.h": "void bn_mul_mont_small(void);\n",
            },
        ):
            self.assertTrue(
                classify_branches.same_named_file_carries_fix(
                    FIX_SHA, ["crypto/fipsmodule/bn/internal.h"], REF
                )
            )

    def test_every_file_the_fix_touched_is_tried(self):
        with fake_branch_files(
            by_name={"params.c": ["crypto/dh/params.c"]},
            removed={"crypto/dh_extra/params.c": ["if (!BN_is_odd(dh->p))"]},
            contents={"crypto/dh/params.c": "  if (!BN_is_odd(dh->p))\n"},
        ):
            self.assertTrue(
                classify_branches.same_named_file_carries_fix(
                    FIX_SHA, [SRC_FILES[0], "crypto/dh_extra/params.c"], REF
                )
            )

    def test_a_fix_touching_nothing_is_not_a_hit(self):
        with fake_branch_files(by_name={}, removed={}, contents={}):
            self.assertFalse(
                classify_branches.same_named_file_carries_fix(FIX_SHA, [], REF)
            )


class ClassifyBranchVerdict(unittest.TestCase):
    # The one copy of the per-branch decision. UNSURE is not a final answer here, the
    # AI step refines those later, so what matters is that nothing unclear is ever
    # called not affected. That is the only mistake that ships a vulnerability.

    def verdict(self, **kwargs):
        """classify_branch with every lookup it makes faked out"""
        with fake_verdict_inputs(**kwargs):
            return classify_branches.classify_branch(
                FIX_SHA, SRC_FILES, BUG_COMMITS, BRANCH
            )

    def test_a_branch_that_already_has_the_fix_is_already_patched(self):
        got = self.verdict(already=True, affected=True, still_present=True)
        self.assertEqual(got, config.ALREADY)

    def test_the_already_patched_check_runs_before_the_line_search(self):
        # Applying a fix deletes the buggy lines, so asking about them first would
        # read False on a patched branch and land it on UNSURE
        with mock.patch.multiple(
            classify_branches,
            is_already_patched=lambda sha, branch: True,
            any_bug_commit_present=never_called,
            buggy_lines_still_present=never_called,
        ):
            got = classify_branches.classify_branch(
                FIX_SHA, SRC_FILES, BUG_COMMITS, BRANCH
            )
        self.assertEqual(got, config.ALREADY)

    def test_a_bug_commit_with_the_lines_still_there_is_affected(self):
        got = self.verdict(affected=True, still_present=True)
        self.assertEqual(got, config.AFFECTED)

    def test_a_bug_commit_with_nothing_to_look_for_is_still_affected(self):
        # None means the fix deleted no distinctive line, which is not evidence the
        # bug is gone. Treating it like False here would clear a real branch
        got = self.verdict(affected=True, still_present=None)
        self.assertEqual(got, config.AFFECTED)

    def test_the_buggy_lines_alone_are_enough_without_a_bug_commit(self):
        # A branch-only commit can write the same bug, so history never finds it
        got = self.verdict(affected=False, still_present=True)
        self.assertEqual(got, config.AFFECTED)

    def test_a_bug_commit_whose_lines_are_gone_is_left_undecided(self):
        got = self.verdict(affected=True, still_present=False, on_branch=True)
        self.assertEqual(got, config.UNSURE)

    def test_no_bug_commit_and_nothing_to_look_for_is_left_undecided(self):
        got = self.verdict(affected=False, still_present=None, on_branch=True)
        self.assertEqual(got, config.UNSURE)

    def test_no_bug_commit_and_the_lines_gone_is_left_undecided(self):
        got = self.verdict(affected=False, still_present=False, on_branch=True)
        self.assertEqual(got, config.UNSURE)

    def test_code_that_is_not_on_the_branch_at_all_is_not_affected(self):
        got = self.verdict(affected=False, still_present=False, on_branch=False)
        self.assertEqual(got, config.NOT_AFFECTED)

    def test_a_bug_commit_cannot_flag_a_branch_that_dropped_the_code(self):
        # The branch shares the history that wrote the bug but not the file, so there
        # is nothing left to fix
        got = self.verdict(affected=True, still_present=False, on_branch=False)
        self.assertEqual(got, config.NOT_AFFECTED)

    def test_a_file_that_only_moved_keeps_the_branch_under_review(self):
        got = self.verdict(
            affected=False, still_present=False, on_branch=False, same_named=True
        )
        self.assertEqual(got, config.UNSURE)

    def test_the_same_named_search_only_runs_when_the_file_is_missing(self):
        # It lists every path on the branch, which is too slow to do when the file was
        # already found at its own path
        with mock.patch.multiple(
            classify_branches,
            is_already_patched=lambda sha, branch: False,
            any_bug_commit_present=lambda commits, ref: False,
            buggy_lines_still_present=lambda sha, files, ref: False,
            get_file_on_branch=lambda file, ref, commit=None: ("code", file),
            same_named_file_carries_fix=never_called,
        ):
            got = classify_branches.classify_branch(
                FIX_SHA, SRC_FILES, BUG_COMMITS, BRANCH
            )
        self.assertEqual(got, config.UNSURE)

    def test_one_missing_file_does_not_clear_a_branch_that_has_another(self):
        files = [SRC_FILES[0], "crypto/dh_extra/params.c"]

        def only_the_second(file, ref, commit=None):
            return ("code", file) if file == files[1] else (None, None)

        with mock.patch.multiple(
            classify_branches,
            is_already_patched=lambda sha, branch: False,
            any_bug_commit_present=lambda commits, ref: False,
            buggy_lines_still_present=lambda sha, files_, ref: False,
            get_file_on_branch=only_the_second,
            same_named_file_carries_fix=lambda sha, files_, ref: False,
        ):
            got = classify_branches.classify_branch(FIX_SHA, files, BUG_COMMITS, BRANCH)
        self.assertEqual(got, config.UNSURE)

    def test_the_file_is_looked_up_through_the_fix_so_renames_are_followed(self):
        # A branch that forked before a rename only has the old path, which
        # get_file_on_branch can only reach when it is handed the fix to walk back
        asked = {}

        def record(file, ref, commit=None):
            asked[file] = commit
            return (None, None)

        with mock.patch.multiple(
            classify_branches,
            is_already_patched=lambda sha, branch: False,
            any_bug_commit_present=lambda commits, ref: False,
            buggy_lines_still_present=lambda sha, files, ref: False,
            get_file_on_branch=record,
            same_named_file_carries_fix=lambda sha, files, ref: False,
        ):
            classify_branches.classify_branch(FIX_SHA, SRC_FILES, BUG_COMMITS, BRANCH)
        self.assertEqual(asked, {SRC_FILES[0]: FIX_SHA})

    def test_the_line_search_is_handed_a_hashable_file_list(self):
        # buggy_lines_still_present is lru_cached, so a list would raise TypeError
        asked = []

        with mock.patch.multiple(
            classify_branches,
            is_already_patched=lambda sha, branch: False,
            any_bug_commit_present=lambda commits, ref: True,
            buggy_lines_still_present=lambda sha, files, ref: asked.append(files),
        ):
            classify_branches.classify_branch(FIX_SHA, SRC_FILES, BUG_COMMITS, BRANCH)
        self.assertEqual(asked, [tuple(SRC_FILES)])

    def test_the_branch_name_is_read_as_an_origin_ref(self):
        asked = []

        with mock.patch.multiple(
            classify_branches,
            is_already_patched=lambda sha, branch: False,
            any_bug_commit_present=lambda commits, ref: asked.append(ref),
            buggy_lines_still_present=lambda sha, files, ref: True,
        ):
            classify_branches.classify_branch(FIX_SHA, SRC_FILES, BUG_COMMITS, BRANCH)
        self.assertEqual(asked, [REF])

    def test_a_fix_with_no_source_files_is_left_undecided(self):
        # This used to clear every branch: any() over no files is False, so the code
        # read as absent everywhere. A merge commit reaches it, since diff-tree shows
        # nothing for one and still exits 0. git stops the run before this now, and
        # this is the second line of defence
        with fake_verdict_inputs(affected=False, still_present=None):
            got = classify_branches.classify_branch(FIX_SHA, [], BUG_COMMITS, BRANCH)
        self.assertEqual(got, config.UNSURE)

    def test_no_source_files_never_reaches_the_lookups(self):
        with mock.patch.multiple(
            classify_branches,
            is_already_patched=never_called,
            any_bug_commit_present=never_called,
            buggy_lines_still_present=never_called,
        ):
            got = classify_branches.classify_branch(FIX_SHA, [], BUG_COMMITS, BRANCH)
        self.assertEqual(got, config.UNSURE)


class ClipToBudget(unittest.TestCase):
    # A file cut off in silence reads to the model as code that is not there, and not
    # there is how a branch gets cleared

    def test_content_that_fits_is_untouched(self):
        self.assertEqual(git.clip_to_budget("int main(void);"), "int main(void);")

    def test_content_at_the_limit_is_untouched(self):
        exactly = "x" * config.MAX_FILE_BYTES
        self.assertEqual(git.clip_to_budget(exactly), exactly)

    def test_a_cut_off_file_says_so(self):
        clipped = git.clip_to_budget("x" * (config.MAX_FILE_BYTES + 500))
        self.assertIn("cut off here", clipped)
        self.assertIn("500 more bytes", clipped)

    def test_the_kept_part_is_the_head_of_the_file(self):
        content = "first line\n" + "x" * config.MAX_FILE_BYTES
        clipped = git.clip_to_budget(content)
        self.assertTrue(clipped.startswith("first line\n"))
        self.assertEqual(
            clipped[: config.MAX_FILE_BYTES], content[: config.MAX_FILE_BYTES]
        )


class ChangedFilesWithStatus(unittest.TestCase):
    # An empty file list clears every branch, so neither a git failure nor a commit
    # with no diff is allowed to come back as one

    def parse(self, returncode=0, stdout="", stderr=""):
        """changed_files_with_status reading a canned diff-tree, without running git"""
        result = subprocess.CompletedProcess(
            args=["git"], returncode=returncode, stdout=stdout, stderr=stderr
        )
        with mock.patch.object(git, "git_in_repo", lambda args, **kw: result):
            return git.changed_files_with_status(FIX_SHA)

    def test_added_files_are_not_traceable(self):
        # A file the fix added has no history on any branch to blame
        changed, traceable = self.parse(stdout="M\tcrypto/aead.c\nA\ttls/new.c\n")
        self.assertEqual(changed, ["crypto/aead.c", "tls/new.c"])
        self.assertEqual(traceable, ["crypto/aead.c"])

    def test_a_rename_is_read_as_its_new_path(self):
        changed, traceable = self.parse(stdout="R100\told.c\tnew.c\n")
        self.assertEqual(changed, ["new.c"])
        self.assertEqual(traceable, ["new.c"])

    def test_a_failed_diff_tree_stops_the_run(self):
        with self.assertRaises(config.BackportError) as caught:
            self.parse(returncode=128, stderr="bad object")
        self.assertIn("bad object", str(caught.exception))

    def test_a_commit_that_changes_nothing_stops_the_run(self):
        # diff-tree prints nothing for a merge commit and still exits 0, which used to
        # report every release branch clean
        with self.assertRaises(config.BackportError) as caught:
            self.parse(stdout="")
        message = str(caught.exception)
        self.assertIn("nothing to analyze", message)
        self.assertIn(f"--commit {FIX_SHA}^..{FIX_SHA}", message)


if __name__ == "__main__":
    unittest.main()
