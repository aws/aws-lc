# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import argparse
import multiprocessing
import os
import re
import subprocess
import sys
import time
import psutil

LINEWIDTH = 80

# A useful hack for trimming off unnecessary output for proofs
# Ultimately, it should be a feature provided by SAW
patterns = [".*Branching.*", ".*Matching.*", ".*Registering.*", \
            ".*Applied.*", ".*Simulating.*", ".*Assume.*", ".*variant.*", \
            ".*Checking.*", ".*Finding.*", ".*Found.*", ".*Examining.*", \
            ".*All.*", ".*Simulation.*", ".*Calling.*", ".*Running.*", \
            ".*Symbolic.*"]
pattern = "(" + ")|(".join(patterns) + ")"

# Parsing one command
# This parser assumes a specific shape of the commands, it should not be used
# for general purpose.
def parse_command(command):
    if not '&&' in command: return [None, command.strip().split(' ')]
    [cdpath, command] = command.split('&&')
    cdpath = cdpath.strip().split(' ')
    command = command.strip().split(' ')
    assert(len(cdpath) == 2 and cdpath[0] == 'cd')

    return [cdpath[1], command]

# Run one command using subprocess
def run_process(command):
    [path, command] = parse_command(command)
    print("Running proof with command {}".format(command))
    if path:
        wd = os.getcwd()
        os.chdir(path)
    start = time.perf_counter()
    result = subprocess.run(["/usr/bin/time"] + command, capture_output = True)
    end = time.perf_counter()
    if path:
        os.chdir(wd)
    print("Finishing proof with command {}".format(command))
    return [result, end - start]

# Create a summary for the proof output
def create_summary(output, error, exit_code, debug):
    output = output.split('\n')
    summary = []
    for l in output:
        if not debug:
            if not l or re.match(pattern, l): continue
            if "Stack frame" in l: break
        summary.append(l)
    if error: summary.append(error)
    summary.append("Exit {}".format(exit_code))
    return '\n'.join(summary)

# Run subprocesses in parallel
def parallel_run (commands, debug):
    mem = psutil.virtual_memory().available
    # Assuming each process uses 10GB memory
    pmem = 10*1024*1024*1024
    pbound = int(mem/pmem)
    np = multiprocessing.cpu_count()
    pool = multiprocessing.Pool(min(np, pbound))
    with pool as p:
        results = p.map(run_process, commands)
        for res in results:
            [r, t] = res
            print('-'*LINEWIDTH)
            print("Proof results for {}: {}s".format(r.args, t))
            output = r.stdout.decode("utf-8")
            error = r.stderr.decode("utf-8")
            exit_code = r.returncode
            print(create_summary(output, error, exit_code, debug))
        if any(r.returncode != 0 for [r, _] in results):
            return 1
    return 0

# Parse the input argument
def parse_commands():
    commands = []
    parser = argparse.ArgumentParser( \
               description = 'Parsing proof commands to be run in parallel.')
    parser.add_argument('--file', type = argparse.FileType('r'), \
                        help = 'the file that contains jobs to be paralleled')
    parser.add_argument('--debug', type = bool, default = False, \
                        help = 'enable debug mode to see the complete output')
    args = parser.parse_args()

    for l in args.file.readlines():
        if not l or l.isspace() or l[0] == '#': continue
        commands.append(l.strip('\n'))

    return [commands, args.debug]

if __name__ == '__main__':
    [commands, debug] = parse_commands()
    exit_code =  parallel_run(commands, debug)
    print("Exit {}".format(exit_code))
    sys.exit(exit_code)
