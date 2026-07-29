"""
Shared vocabulary for the backport CLI.

Layer: foundation (leaf). Imported by every other module; depends on nothing
internal, so it can never be part of an import cycle.

This is the leaf module every other one can import without risking a cycle: the
four verdict states, their display labels, and the single user-facing error type.
"""

# --------------------------------------------------------------------------
# Verdict states
# --------------------------------------------------------------------------
#
# Every branch ends up in exactly one of these buckets. The deterministic engine
# only ever emits a confident NOT_AFFECTED when the changed code is provably
# absent; anything it cannot confirm becomes UNSURE and is handed to the AI layer
# (or, under --no-ai, flagged AFFECTED for review). So a real backport is never
# silently dropped.

AFFECTED = "affected"
NOT_AFFECTED = "not_affected"
UNSURE = "unsure"
ALREADY = "already_patched"

# Human-readable labels for the analyze table.
LABEL = {
    AFFECTED: "AFFECTED",
    NOT_AFFECTED: "not affected",
    UNSURE: "UNSURE",
    ALREADY: "already patched",
}


# --------------------------------------------------------------------------
# Errors
# --------------------------------------------------------------------------


class BackportError(Exception):
    """A user-facing failure (bad ref, patch won't apply, no saved run, etc.).

    `main` catches this, prints it as a clean ``error: ...`` line, and exits 1 --
    as opposed to an unexpected exception, which surfaces its full traceback.
    """
