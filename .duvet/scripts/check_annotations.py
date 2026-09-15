#!/usr/bin/env python3
"""Guard against Duvet annotation regressions in aws-lc.

Duvet's JSON report is the authoritative parser for the `//=` citation
annotations in source. This script snapshots the set of source-code
annotations it finds and fails when any snapshotted annotation disappears —
i.e. someone deleted or broke a `//=` citation. Adding new annotations never
fails the check; it just reminds you to refresh the baseline with --update.

Usage:
  check_annotations.py            # compare against committed baseline (CI)
  check_annotations.py --update   # rewrite the baseline after intentional edits
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path

DUVET_DIR = Path(__file__).resolve().parent.parent
REPO_ROOT = DUVET_DIR.parent
BASELINE = DUVET_DIR / "annotations.baseline"


def collect_annotations() -> list[str]:
    """Run `duvet report` and return normalized source-code annotation rows.

    A row is `<target_url>#<section>\t<impl|test>\t<source_file>\t<line>`. SPEC
    rows (the requirement .toml files themselves) are excluded — we only track
    the citations that live in shippable source. The source line is part of the
    key so two distinct citations to the same (section, kind, file) can't mask
    each other's removal in the multiset diff (a citation deleted at one line
    while an unrelated one is added at another would otherwise net to zero).
    """
    with tempfile.TemporaryDirectory() as tmpdir:
        json_path = Path(tmpdir) / "report.json"
        try:
            subprocess.run(
                ["duvet", "report", "--json", str(json_path)],
                cwd=REPO_ROOT,
                check=True,
                capture_output=True,
                text=True,
            )
        except FileNotFoundError:
            print("ERROR: `duvet` not found on PATH", file=sys.stderr)
            raise SystemExit(1)
        except subprocess.CalledProcessError as e:
            print("ERROR: `duvet report` failed with:\n" + (e.stderr or e.stdout or ""),
                  file=sys.stderr)
            raise SystemExit(1)
        report = json.loads(json_path.read_text())

    rows: list[str] = []
    for ann in report["annotations"]:
        if ann.get("type") == "SPEC":
            continue
        kind = "test" if ann.get("type") == "TEST" else "impl"
        rows.append(
            f"{ann['target_path']}#{ann['target_section']}\t{kind}\t{ann['source']}\t{ann['line']}"
        )
    return sorted(rows)


def write_baseline(rows: list[str]) -> None:
    BASELINE.write_text("\n".join(rows) + "\n")
    print(f"Wrote {len(rows)} annotations to {BASELINE.relative_to(REPO_ROOT)}")


def check(rows: list[str]) -> int:
    if not BASELINE.exists():
        print(f"ERROR: baseline missing at {BASELINE.relative_to(REPO_ROOT)}", file=sys.stderr)
        print("Run: python3 .duvet/scripts/check_annotations.py --update", file=sys.stderr)
        return 1

    baseline = [ln for ln in BASELINE.read_text().splitlines() if ln.strip()]
    have = Counter(rows)
    want = Counter(baseline)

    removed = want - have  # multiset: baseline entries no longer present
    if removed:
        print("Duvet annotation regression: the following citations were removed or broken:\n", file=sys.stderr)
        for row, count in sorted(removed.items()):
            url, kind, src, line = row.split("\t")
            for _ in range(count):
                print(f"  - [{kind}] {url}\n      in {src}:{line}", file=sys.stderr)
        print(
            "\nRestore the annotation, or if the removal is intentional refresh the baseline:\n"
            "  python3 .duvet/scripts/check_annotations.py --update",
            file=sys.stderr,
        )
        return 1

    added = have - want
    if added:
        print(f"{sum(added.values())} new annotation(s) found (not a regression).")
        print("Refresh the baseline to record them: python3 .duvet/scripts/check_annotations.py --update")

    print(f"OK: all {len(baseline)} baselined annotations present.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--update", action="store_true", help="rewrite the baseline instead of checking")
    args = parser.parse_args()

    rows = collect_annotations()
    if args.update:
        write_baseline(rows)
        return 0
    return check(rows)


if __name__ == "__main__":
    sys.exit(main())
