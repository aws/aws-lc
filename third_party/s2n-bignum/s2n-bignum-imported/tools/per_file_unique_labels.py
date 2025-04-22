import glob
import re
import os

# For matched files, attempts to discover labels and convert them to per-file
# unique labels.
#
# To run:
#  1) Add list of folders+file extension under "main"
#  2) Run "python3 ./per_file_unique_labels.py" from root of s2n-bignum
#
# This script does not capture all possible labels for all flavors of
# assembly language. For example, it doesn't catch local NASM-style labels.
def append_labels_with_file_name(directory, match):

  matched_files = glob.glob(directory + match)

  print('file names: {}'.format(matched_files))

  for fname in matched_files:
    with open(fname, "r+") as file:
      name_of_file = os.path.basename(fname).strip('.S')
      print('\nfile name: {}'.format(name_of_file))

      labels = []
      data_get_labels = []
      data_all_replaced = []

      for line in file:
        match = re.search('^[a-z0-9_]+:', line)
        data_get_labels.append(re.sub('^([a-z0-9_]+):', name_of_file + "_\\1:", line))

        # Only pick matches and matches that start at index 0
        # should ensure we actually only pick labels!
        if match != None and match.start() == 0:
          labels.append(match.string.strip().strip(':'))

      # Ensure no duplicates
      if len(labels) > len(set(labels)):
        sys.exit("duplicate labels discovered...")

      print("known labels:\n{}".format(labels))

      for line in data_get_labels:

        new_line = ""

        for known_labels in labels:
          new_line = re.sub('^((?!/).*)(' + known_labels + ')((?!:).*)$', "\\1" + name_of_file + "_\\2\\3", line)
          if new_line != line:
            break

        data_all_replaced.append(new_line)

      # Need to go back to start again since the read into memory moved
      # the read pointer to the end
      data_to_string = ''.join(data_all_replaced)
      file.seek(0)
      file.write(data_to_string)

if __name__ == '__main__':

  # Manually add folders and file extension.
  # Below is an example
  append_labels_with_file_name('./x86/curve25519/', '*.S')
  append_labels_with_file_name('./x86_att/curve25519/', '*.S')
  append_labels_with_file_name('./arm/curve25519/', '*.S')

  # For test
  #append_labels_with_file_name('./x86/curve25519/', 'curve25519_x25519_alt.S')
