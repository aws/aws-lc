# coding=utf8

# Copyright (c) 2015, Google Inc.
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
# SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
# OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
# CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

import io
import optparse
import os
import subprocess
import sys
import json
import tarfile
import time
import bz2
from string import Template

# OS_ARCH_COMBOS maps from OS and platform to the OpenSSL assembly "style" for
# that platform and the extension used by asm files.
OS_ARCH_COMBOS = [
    ('ios', 'arm', 'ios32', [], 'S'),
    ('ios', 'aarch64', 'ios64', [], 'S'),
    ('linux', 'arm', 'linux32', [], 'S'),
    ('linux', 'aarch64', 'linux64', [], 'S'),
    ('linux', 'ppc64le', 'linux64le', [], 'S'),
    ('linux', 'x86', 'elf', ['-fPIC'], 'S'),
    ('linux', 'x86_64', 'elf', [], 'S'),
    ('mac', 'x86', 'macosx', ['-fPIC'], 'S'),
    ('mac', 'x86_64', 'macosx', [], 'S'),
    ('win', 'x86', 'win32n', [], 'asm'),
    ('win', 'x86_64', 'nasm', [], 'asm'),
    ('win', 'aarch64', 'win64', [], 'S'),
]

def FindCMakeFiles(directory):
  """Returns list of all CMakeLists.txt files recursively in directory."""
  cmakefiles = []

  for (path, _, filenames) in os.walk(directory):
    for filename in filenames:
      if filename == 'CMakeLists.txt':
        cmakefiles.append(os.path.join(path, filename))

  return cmakefiles

def FindCFiles(directory, filter_func):
  """Recurses through directory and returns a list of paths to all the C source
  files that pass filter_func."""
  cfiles = []

  for (path, dirnames, filenames) in os.walk(directory):
    for filename in filenames:
      if not filename.endswith('.c') and not filename.endswith('.cc'):
        continue
      if not filter_func(path, filename, False):
        continue
      cfiles.append(os.path.relpath(os.path.join(path, filename), DEST_DIR))

    for (i, dirname) in enumerate(dirnames):
      if not filter_func(path, dirname, True):
        del dirnames[i]

  cfiles.sort()
  return cfiles

def ExtractPerlAsmFromCMakeFile(cmakefile):
  """Parses the contents of the CMakeLists.txt file passed as an argument and
  returns a list of all the perlasm() directives found in the file."""
  perlasms = []
  with io.open(cmakefile, encoding="utf-8") as f:
    for line in f:
      line = line.strip()
      if not line.startswith('perlasm('):
        continue
      if not line.endswith(')'):
        raise ValueError('Bad perlasm line in %s' % cmakefile)
      # Remove "perlasm(" from start and ")" from end
      params = line[8:-1].split()
      if len(params) < 2:
        raise ValueError('Bad perlasm line in %s' % cmakefile)
      perlasms.append({
          'extra_args': params[2:],
          'input': os.path.join(os.path.dirname(cmakefile), params[1]),
          'output': os.path.join(os.path.relpath(os.path.dirname(cmakefile), SRC_DIR), params[0])
      })

  return perlasms

def ReadPerlAsmOperations():
  """Returns a list of all perlasm() directives found in CMake config files in
  src_dir"""
  perlasms = []
  cmakefiles = FindCMakeFiles(SRC_DIR)

  for cmakefile in cmakefiles:
    perlasms.extend(ExtractPerlAsmFromCMakeFile(cmakefile))

  return perlasms


def PerlAsm(output_filename, input_filename, perlasm_style, extra_args):
  """Runs the a perlasm script and puts the output into output_filename."""
  base_dir = os.path.dirname(output_filename)
  if not os.path.isdir(base_dir):
    os.makedirs(base_dir)
  subprocess.check_call(
      ['perl', input_filename, perlasm_style, output_filename] + extra_args)


def ArchForAsmFilename(filename):
  """Returns the architectures that a given asm file should be compiled for
  based on substrings in the filename."""

  if 'x86_64' in filename or 'avx2' in filename or 'avx512' in filename:
    return ['x86_64']
  elif ('x86' in filename and 'x86_64' not in filename) or '586' in filename:
    return ['x86']
  elif 'armx' in filename:
    return ['arm', 'aarch64']
  elif 'armv8' in filename:
    return ['aarch64']
  elif 'arm' in filename:
    return ['arm']
  elif 'ppc' in filename:
    return ['ppc64le']
  else:
    raise ValueError('Unknown arch for asm filename: ' + filename)


def WriteAsmFiles(perlasms):
  """Generates asm files from perlasm directives for each supported OS x
  platform combination."""

  for osarch in OS_ARCH_COMBOS:
    (osname, arch, perlasm_style, extra_args, asm_ext) = osarch
    key = (osname, arch)
    outDir = os.path.join(DEST_DIR, ('%s-%s' % key))

    for perlasm in perlasms:
      filename = os.path.basename(perlasm['input'])
      output = perlasm['output']
      output = os.path.relpath(os.path.join(outDir, output), DEST_DIR)
      output = output.replace('${ASM_EXT}', asm_ext)

      if arch in ArchForAsmFilename(filename):
        PerlAsm(os.path.join(DEST_DIR, output), perlasm['input'], perlasm_style,
                perlasm['extra_args'] + extra_args)

def ExtractVariablesFromCMakeFile(cmakefile):
  """Parses the contents of the CMakeLists.txt file passed as an argument and
  returns a dictionary of exported source lists."""
  variables = {}
  in_set_command = False
  set_command = []
  with open(cmakefile) as f:
    for line in f:
      if '#' in line:
        line = line[:line.index('#')]
      line = line.strip()

      if not in_set_command:
        if line.startswith('set('):
          in_set_command = True
          set_command = []
      elif line == ')':
        in_set_command = False
        if not set_command:
          raise ValueError('Empty set command')
        variables[set_command[0]] = set_command[1:]
      else:
        set_command.extend([c for c in line.split(' ') if c])

  if in_set_command:
    raise ValueError('Unfinished set command')
  return variables

def create_deterministic_tar_bz2(input_file, output_file):
  # Use a fixed timestamp (Unix epoch)
  fixed_time = 0  # January 1, 1970, 00:00:00 UTC

  # An object to hold the tar content
  tar_data = io.BytesIO()

  with tarfile.open(fileobj=tar_data, mode="w:", format=tarfile.PAX_FORMAT) as tar:
    # Ensure consistent metadata across platforms
    tarinfo = tarfile.TarInfo(name=os.path.basename(input_file))
    tarinfo.mtime = fixed_time
    tarinfo.mode = 0o644
    tarinfo.uid = 0
    tarinfo.gid = 0
    tarinfo.uname = ""
    tarinfo.gname = ""

    with open(input_file, "rb") as file:
      file_data = file.read()
      tarinfo.size = len(file_data)
      tar.addfile(tarinfo, io.BytesIO(file_data))

  # Obtain content for compression
  tar_content = tar_data.getvalue()

  # Use a consistent compression level
  bz2_data = bz2.compress(tar_content, compresslevel=9)

  with open(output_file, 'wb') as output:
    output.write(bz2_data)

def main():
  cmake = ExtractVariablesFromCMakeFile(os.path.join(SRC_DIR, 'sources.cmake'))

  # Generate err_data.c
  if not os.path.isdir(DEST_DIR):
    os.makedirs(DEST_DIR)

  with open(os.path.join(DEST_DIR, 'err_data.c'), 'w+') as err_data:
    subprocess.check_call(['go', 'run', 'err_data_generate.go'],
                          cwd=os.path.join(SRC_DIR, 'crypto', 'err'),
                          stdout=err_data)

  ctd_path = os.path.join(DEST_DIR, 'crypto_test_data.cc')
  ctd_gz_path = os.path.join(DEST_DIR, 'crypto_test_data.cc.tar.bz2')

  # Generate crypto_test_data.cc
  with open(ctd_path, 'w+') as out:
    subprocess.check_call(
        ['go', 'run', 'util/embed_test_data.go'] + cmake['CRYPTO_TEST_DATA'],
        cwd=SRC_DIR,
        stdout=out)

  create_deterministic_tar_bz2(ctd_path, ctd_gz_path)
  os.remove(ctd_path)

  WriteAsmFiles(ReadPerlAsmOperations())

  return 0

if __name__ == '__main__':
  usage = '''%prog

  This script generates intermediate build files for CMake builds without the
  need to install Go or Perl as a dependency. These files are output to the
  |generated-src| directory and are used by the top-level CMakeLists.txt if
  either Go or Perl are not found.
  '''

  parser = optparse.OptionParser(usage=usage)
  options, args = parser.parse_args(sys.argv[1:])

  SRC_DIR = os.getcwd()
  DEST_DIR = os.path.relpath('generated-src', os.getcwd())

  sys.exit(main())
