#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""Parse gtest JSON reports and write a GitHub Actions step summary."""

import json
import glob
import os
import sys

def parse_reports(report_dir):
    """Parse all JSON reports and return per-suite timing data."""
    suites = {}  # {test_binary: {shard_times: [], total: float, slowest_tests: []}}

    for f in sorted(glob.glob(os.path.join(report_dir, "*_shard_*.json"))):
        basename = os.path.basename(f)
        # e.g. crypto_test_shard_2.json -> crypto_test
        parts = basename.rsplit("_shard_", 1)
        suite_name = parts[0]

        with open(f) as fh:
            data = json.load(fh)

        shard_time = float(data.get("time", "0s").rstrip("s"))

        if suite_name not in suites:
            suites[suite_name] = {"shard_times": [], "slowest_tests": []}

        suites[suite_name]["shard_times"].append(shard_time)

        # Collect individual test times
        for ts in data.get("testsuites", []):
            for test in ts.get("testsuite", []):
                t = float(test.get("time", "0s").rstrip("s"))
                suites[suite_name]["slowest_tests"].append(
                    (t, f"{ts['name']}.{test['name']}")
                )

    return suites


def write_summary(suites, output):
    """Write markdown summary to output file."""
    lines = []
    lines.append("## 🧪 gtest Timing Summary\n")
    lines.append("| Test Binary | Wall-clock (longest shard) | Shards | Total tests |")
    lines.append("|-------------|---------------------------|--------|-------------|")

    for name, data in sorted(suites.items(), key=lambda x: max(x[1]["shard_times"]), reverse=True):
        longest = max(data["shard_times"])
        num_shards = len(data["shard_times"])
        num_tests = len(data["slowest_tests"])
        if longest >= 60:
            time_str = f"{longest/60:.1f}m"
        else:
            time_str = f"{longest:.1f}s"
        lines.append(f"| `{name}` | {time_str} | {num_shards} | {num_tests} |")

    # Top 5 slowest individual tests across all suites
    all_tests = []
    for data in suites.values():
        all_tests.extend(data["slowest_tests"])
    all_tests.sort(reverse=True)

    if all_tests:
        lines.append("\n### ⏱️ Top 5 Slowest Tests\n")
        lines.append("| Test | Time |")
        lines.append("|------|------|")
        for t, name in all_tests[:5]:
            if t >= 60:
                time_str = f"{t/60:.1f}m"
            else:
                time_str = f"{t:.1f}s"
            disabled = " ⚠️" if "DISABLED_" in name else ""
            lines.append(f"| `{name}`{disabled} | {time_str} |")

    lines.append("")
    output.write("\n".join(lines))


def main():
    report_dir = sys.argv[1] if len(sys.argv) > 1 else os.environ.get(
        "GTEST_REPORT_DIR", "test_reports"
    )

    if not os.path.isdir(report_dir):
        print(f"No report directory found at {report_dir}", file=sys.stderr)
        sys.exit(0)  # Don't fail the build

    reports = glob.glob(os.path.join(report_dir, "*_shard_*.json"))
    if not reports:
        print(f"No JSON reports found in {report_dir}", file=sys.stderr)
        sys.exit(0)

    suites = parse_reports(report_dir)

    # Write to GITHUB_STEP_SUMMARY if available, otherwise stdout
    summary_file = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary_file:
        with open(summary_file, "a") as f:
            write_summary(suites, f)
    else:
        write_summary(suites, sys.stdout)


if __name__ == "__main__":
    main()
