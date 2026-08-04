"""
Every word sent to the model, kept apart from the logic that sends it
Wording here is what makes the AI's answers useful, so change it carefully
"""

SYSTEM_PROMPT = (
    "You are a security-focused code review assistant in an automated CVE "
    "backport pipeline for AWS-LC, Amazon's cryptographic library. Decide whether "
    "a release branch is affected by a vulnerability that was fixed on main.\n\n"
    "- Your analysis is ADVISORY. A human reads it, nothing is applied "
    "automatically.\n"
    "- Do not speculate past what the code shows.\n"
    "- A file reported as not present on the branch (checked across rename "
    "history) is positive evidence the branch predates the code, not missing "
    "information.\n"
    "- If the diff or file contents are truncated or genuinely unclear, say so and "
    "lower your confidence.\n"
    "- Answer in plain Markdown."
)

# read_answer() parses these four lines back out, so the labels have to stay
ANSWER_FORMAT = (
    "Respond with:\n"
    "- **Likely affected**: Yes / No / Uncertain\n"
    "- **Confidence**: high / medium / low\n"
    "- **Reasoning**: 2-4 sentences\n"
    "- **Recommendation**: one line for the human reviewer"
)

# Asked when git history flagged the branch, to look for a false positive
AUDITOR_TASK = (
    "---\n"
    "Git history flagged `{branch}` as AFFECTED: a commit that wrote the patched "
    "lines is in its history. That check takes the OLDEST commit to touch those "
    "lines, which over-flags when the lines come from imported third-party code "
    "(say a bulk BoringSSL import) that predates every release branch and was "
    "never vulnerable here. Audit for that false positive.\n\n"
    "1. Is the vulnerable code in the diff really present and reachable here, or "
    "is the match coming from imported boilerplate?\n"
    "2. Does the fix change behaviour? A rename, a reformat, or a comment-only "
    "edit neither adds nor removes a vulnerability, so say so if that is all it "
    "is.\n"
    "3. Is there concrete evidence this branch is not impacted despite the "
    "history match? Without strong evidence, assume the flag is correct.\n"
    "4. How confident are you, and why?\n\n" + ANSWER_FORMAT
)

# Asked when git history could not decide either way
TIEBREAKER_TASK = (
    "---\n"
    "Git history could not settle this branch. Assess:\n\n"
    "1. Does the branch likely hold the vulnerable code in the diff?\n"
    "2. If so, does the fix still apply in spirit, even if a cherry-pick would "
    "conflict on diverged context?\n"
    "3. How confident are you, and why?\n\n" + ANSWER_FORMAT
)

ALL_ABSENT_NOTE = (
    "\n\nNone of the fixed files exist here under any name. That nearly always "
    "means the vulnerable code arrived after this branch diverged, so the branch "
    "is NOT affected. Only withhold that unless you can point to the same logic "
    "in a differently named file here."
)

SOME_ABSENT_NOTE = (
    "\n\nThese files are absent, most likely added after this branch diverged. "
    "Base your assessment on the files shown above."
)

BUGGY_LINES_GONE_NOTE = (
    "\n\n### The deleted lines are ABSENT here\n"
    "The exact lines this fix changes or removes are not on this branch, matched "
    "ignoring whitespace and comments. That is strong evidence the vulnerable "
    "path does not exist here. Treat the branch as NOT affected unless you can "
    "point to the same logic in a materially refactored form."
)
