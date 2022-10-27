# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

import sys
import pandas as pd
import numpy as np
import csv

from compare_results import read_data


def main():
    if len(sys.argv) != 3:
        print("Usage: update_results.py [file to update] [new file]", file=sys.stderr)
        sys.exit(1)

    file1 = sys.argv[1]
    file2 = sys.argv[2]

    if not file1.endswith(".csv") or not file2.endswith(".csv"):
        print("Provided files must be .csv files", file=sys.stderr)
        sys.exit(1)

    # read contents of files into a dataframe in preparation for update
    df1 = read_data(file1)
    df2 = read_data(file2)

    # set the dataframe index to be the unique description of each algorithm
    # we can do the below because we're assuming that we're working on output from the speed tool converted into a csv
    df1.set_index(list(df1.columns[[0]]), inplace=True)
    df2.set_index(list(df2.columns[[0]]), inplace=True)

    # update df1 with the contents of df2
    df1.update(df2)

    # reset the index to recover initial structures
    df1.reset_index(inplace=True)
    df2.reset_index(inplace=True)

    # we want the first row of the file to contain the input filename so users can freely rename the output file while still
    # retaining whatever information the input file name held (e.g. cpu type, benchmarks run, etc.)
    num_cols = df1.shape[1]
    labels = []
    for i in range(num_cols):
        # we want the 2nd column to contain the title information (useful for clear output when the output of this script
        # is used in convert_json_to_csv.py)
        if not i == 1:
            labels.append("")
        else:
            labels.append(file1)

    # we will modify the file in place
    output_file = open(file1, 'w', newline='')
    csv_writer = csv.writer(output_file)
    csv_writer.writerow(labels)
    df1.to_csv(output_file, mode='a')
    output_file.close()


if __name__ == "__main__":
    main()
