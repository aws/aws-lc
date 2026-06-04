#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""Parse gtest JSON reports and write a GitHub Actions step summary."""

import glob
import json
import os
import sys


def main():
    report_dir = sys.argv[1] if len(sys.argv) > 1 else os.environ.get(
        "GTEST_REPORT_DIR", "gtest_reports"
    )

    if not os.path.isdir(report_dir):
        print(f"No report directory found at {report_dir}", file=sys.stderr)
        sys.exit(0)

    files = sorted(glob.glob(os.path.join(report_dir, "*.json")))
    if not files:
        print(f"No JSON reports found in {report_dir}", file=sys.stderr)
        sys.exit(0)

    all_tests = []  # (name, seconds, status, binary)

    for f in files:
        binary = os.path.basename(f).rsplit("_shard_", 1)[0]
        try:
            with open(f) as fh:
                data = json.load(fh)
        except (json.JSONDecodeError, IOError):
            continue

        for suite in data.get("testsuites", []):
            suite_name = suite.get("name", "")
            for test in suite.get("testsuite", []):
                name = f"{suite_name}.{test.get('name', '')}"
                time_str = test.get("time", "0s")
                secs = float(time_str.rstrip("s")) if time_str.endswith("s") else float(time_str)
                status = "PASS" if test.get("failures") is None and test.get("result") != "SUPPRESSED" else "FAIL"
                all_tests.append((name, secs, status, binary))

    if not all_tests:
        sys.exit(0)

    all_tests.sort(key=lambda x: x[1], reverse=True)

    total = len(all_tests)
    failed = sum(1 for t in all_tests if t[2] != "PASS")

    lines = []
    lines.append("## 🧪 Test Timing Summary\n")
    lines.append(f"**{total}** tests across {len(files)} report(s), **{failed}** failed\n")
    lines.append("### ⏱️ Top 20 Slowest Tests\n")
    lines.append("| Test | Time | Binary |")
    lines.append("|------|------|--------|")
    for name, secs, status, binary in all_tests[:20]:
        if secs >= 60:
            time_str = f"{secs/60:.1f}m"
        else:
            time_str = f"{secs:.1f}s"
        icon = "" if status == "PASS" else " ❌"
        lines.append(f"| `{name}`{icon} | {time_str} | {binary} |")

    lines.append("")
    sys.stdout.write("\n".join(lines))


if __name__ == "__main__":
    main()
