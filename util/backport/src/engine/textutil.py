"""
Text/line normalizers: comment-, whitespace- and boilerplate-aware helpers.

Layer: impact core (``engine`` package). Builds on nothing.
"""

import re

# ---------------------------------------------------------------------------
# 4. Text / line normalizers
# ---------------------------------------------------------------------------


def norm_ws(s):
    """Collapse runs of whitespace so a reformatted line still matches."""
    return re.sub(r"\s+", " ", s).strip()


_C_FAMILY_EXT = (".c", ".cc", ".cpp", ".cxx", ".h", ".hpp", ".hh", ".hxx")


def is_c_file(file):
    """True for C/C++ source/headers, where '#' is a preprocessor directive
    (real code), not a comment."""
    return file is not None and file.lower().endswith(_C_FAMILY_EXT)


def is_noise_line(s, file=None):
    """True for lines with no vulnerable-code signal: comments, blanks, pure
    punctuation/braces. '#' is a comment only in non-C files; in C/C++ it is a
    preprocessor directive (real code) and is kept."""
    s = s.strip()
    if not s:
        return True
    if s.startswith(("//", "/*", "*/", "*")):  # C/C++ comments
        return True
    if s.startswith("#") and not is_c_file(file):  # script/config comment
        return True
    if set(s) <= set("{}();,: \t"):  # punctuation only
        return True
    return False


def is_boilerplate_line(s):
    """True for real-but-undistinctive lines (bare control-flow, #include, a lone
    string literal) that match too many files to be a reliable pre-image. Skipping
    them only weakens a match, so it is false-negative safe."""
    s = s.strip()
    if re.match(r"^(return|break|continue|goto)\b[^;{}]*;?$", s):
        return True
    if s.startswith("#include"):
        return True
    # Substance is only a string/char literal: strip quoted spans, require enough
    # remaining alnum to be distinctive.
    without_strings = re.sub(r'"(?:[^"\\]|\\.)*"|\'(?:[^\'\\]|\\.)*\'', "", s)
    if len(re.sub(r"\W", "", without_strings)) < 6:
        return True
    return False
