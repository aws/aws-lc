# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

import sys
import pandas as pd
import csv

def main():
    if len(sys.argv) < 2 or len(sys.argv) > 3:
        print("Usage: json_to_csv.py [file to convert] [optional output file name]")
        sys.exit(1)

    input_file = sys.argv[1]

    if not input_file:
        print("Must provide a json file to be converted.")
        sys.exit(1)

    if not input_file.endswith(".json"):
        print("Input file must be a json file.")
        sys.exit(1)

    # Default the name of the output file to that of the input file, just with a .csv instead of a .json
    if len(sys.argv) == 2:
        output_file_name = input_file.replace(".json", ".csv")
    else:
        output_file_name = sys.argv[2]

        # if the provided output file doesn't end with a '.csv' then we want to make it end with a '.csv'
        if not output_file_name.endswith(".csv"):
            output_file_name += ".csv"

    print("Converting {} to {}.".format(input_file, output_file_name))

    df = pd.read_json(input_file)

    # we want the first row of the file to contain the input filename so users can freely rename the output file while still
    # retaining whatever information the input file name held (e.g. cpu type, benchmarks run, etc.)
    num_cols = df.shape[1]
    labels = []
    for i in range(num_cols):
        # we want the 2nd column to contain the title information (useful for clear output when the output of this script
        # is used in convert_json_to_csv.py)
        if not i == 1:
            labels.append("")
        else:
            labels.append(input_file)

    output_file = open(output_file_name, 'w', newline='')
    csv_writer = csv.writer(output_file)
    csv_writer.writerow(labels)
    df.to_csv(output_file, mode='a')
    output_file.close()


if __name__ == "__main__":
    main()