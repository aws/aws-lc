# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import sys
import pandas as pd
import numpy as np

from compare_results import read_data


def main():
    if len(sys.argv) != 3:
        print("Usage: make_metadata.py [file1] [output file]", file=sys.stderr)
        sys.exit(1)

    file = sys.argv[1]
    output_file = sys.argv[2]
    compared_df = read_data(file)

    # we want to differentiate between regressions in pr vs prod (fips) and pr vs prod (non-fips)
    endstr = "mainline."
    if "fips" in file:
        endstr = "mainline (FIPS)."

    # write details of regression in human-readable format to metadata.txt
    with open(output_file, "a") as f:
        f.write("Contents of {}.\n".format(file))
        for index, row in compared_df.iterrows():
            f.write("Performance of {} in PR is {}% slower than {}\n".format(
                row['description.2'],
                round(abs(row['Percentage Difference']), 2),
                endstr))


if __name__ == "__main__":
    main()
