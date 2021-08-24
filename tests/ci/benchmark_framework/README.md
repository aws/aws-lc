## Overview
This folder contains various scripts and tools used by the benchmarking framework in order to process results obtained by the AWS-LC benchmarking tool.

As such, they can also be used to process results obtained when using the AWS-LC benchmarking tool separately from the framework itself.

**Please note:** All python scripts present in this directory expect either output from AWS-LC's benchmarking tools or BoringSSL's speed tool. Thus, it is not guaranteed to work as expected should files from other sources be used.

### `compare_results.py`
This tool compares the output of two different runs of AWS-LC's benchmarking tool. It will output a file with the results of two runs displayed next to each other, with an added column for the performance difference between the two.

Usage is as follows:  `compare_results.py [file1] [file2] [output filename]`

### `convert_json_to_csv.py`
This tool converts the json output of AWS-LC's benchmarking tools and BoringSSL's speed into a .csv file for a more organized and human-readable format.

Usage is as follows: `Usage: json_to_csv.py [file to convert] [optional output file name]`

### `install_docker.sh`
This tool installs docker if it is not already installed. It requires an environment variable denoting the CPU type to work properly.

Usage is as follows:
```
export CPU_TYPE=amd64 # use amd64 for x86 processors, arm64 for arm processors, etc.
./install_docker.sh
```

### `update_results.py`
The benchmarking framework uses this tool in order to update results obtained form a benchmarking run. Namely, this is used to update the TrustToken benchmark results after they are run sequentially (running them in parallel caused severe bias problems).

Usage is as follows: `Usage: update_results.py [file to update] [new file]`