#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""Parse Chromium JSON test results and write a GitHub Actions step summary."""

import glob
import json
import os
import sys


def main():
    report_pattern = sys.argv[1] if len(sys.argv) > 1 else "test_results_*.json"

    files = sorted(glob.glob(report_pattern))
    if not files:
        print(f"No reports matching {report_pattern}", file=sys.stderr)
        sys.exit(0)

    lines = []
    lines.append("## 🧪 Test Timing Summary\n")

    all_timed = []
    total_tests = 0
    total_passed = 0
    total_failed = 0

    for report_file in files:
        with open(report_file) as f:
            data = json.load(f)

        tests = data.get("tests", {})
        if not tests:
            continue

        label = os.path.basename(report_file).replace("test_results_", "").replace(".json", "")
        total_tests += len(tests)
        total_passed += sum(1 for t in tests.values() if t["actual"] == "PASS")
        total_failed += sum(1 for t in tests.values() if t["actual"] not in ("PASS", "SKIP"))

        for name, t in tests.items():
            if t.get("time", 0) > 0:
                all_timed.append((name, t["time"], t["actual"], label))

    all_timed.sort(key=lambda x: x[1], reverse=True)

    lines.append(f"**{total_passed}** passed, **{total_failed}** failed, **{total_tests}** total across {len(files)} build config(s)\n")

    if all_timed:
        lines.append("### ⏱️ Top 10 Slowest Tests\n")
        lines.append("| Test | Time | Config | Status |")
        lines.append("|------|------|--------|--------|")
        for name, secs, status, label in all_timed[:10]:
            if secs >= 60:
                time_str = f"{secs/60:.1f}m"
            else:
                time_str = f"{secs:.1f}s"
            icon = "✅" if status == "PASS" else "❌"
            lines.append(f"| `{name}` | {time_str} | {label} | {icon} |")

    lines.append("")
    sys.stdout.write("\n".join(lines))


if __name__ == "__main__":
    main()
