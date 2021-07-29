import sys
import pandas as pd
import numpy as np
import csv

if len(sys.argv) < 2 or len(sys.argv) > 3:
    print("Usage: json_to_csv.py [file to convert] [optional output file name]")
    sys.exit(1)

input_file = sys.argv[1]

if not input_file:
    print("Must provide a json file to be converted.")
    sys.exit(1)

# Default the name of the output file to that of the input file, just with a .csv instead of a .json
if len(sys.argv) == 2:
    output_file = input_file.replace(".json", ".csv")
else:
    output_file = sys.argv[2]

    # if the provided output file doesn't end with a '.csv' then we want to make it end with a '.csv'
    if not output_file.endswith(".csv"):
        output_file += ".csv"

print("Converting {} to {}.".format(input_file, output_file))

labels = ["", input_file, "", "", ""]

if not input_file.endswith(".json"):
    print("Input file must be a json file.")
    sys.exit(1)

df = pd.read_json(input_file)

output_file = open(output_file, 'w', newline='')
csv_writer = csv.writer(output_file)
csv_writer.writerow(labels)
df.to_csv(output_file, mode='a')
output_file.close()
