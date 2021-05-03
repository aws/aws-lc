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

"""Enumerates source files for consumption by various build systems."""

import io
import optparse
import os
import subprocess
import sys
import json
from string import Template

# OS_ARCH_COMBOS maps from OS and platform to the OpenSSL assembly "style" for
# that platform and the extension used by asm files.
OS_ARCH_COMBOS = [
    ('ios', 'arm', 'ios32', [], 'S'),
    ('ios', 'aarch64', 'ios64', [], 'S'),
    ('linux', 'arm', 'linux32', [], 'S'),
    ('linux', 'aarch64', 'linux64', [], 'S'),
    ('linux', 'ppc64le', 'linux64le', [], 'S'),
    ('linux', 'x86', 'elf', ['-fPIC', '-DOPENSSL_IA32_SSE2'], 'S'),
    ('linux', 'x86_64', 'elf', [], 'S'),
    ('mac', 'x86', 'macosx', ['-fPIC', '-DOPENSSL_IA32_SSE2'], 'S'),
    ('mac', 'x86_64', 'macosx', [], 'S'),
    ('win', 'x86', 'win32n', ['-DOPENSSL_IA32_SSE2'], 'asm'),
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

def OnlyFIPSFragments(path, dent, is_dir):
  return is_dir or (path.startswith(
      os.path.join(SRC_DIR, 'crypto', 'fipsmodule', '')) and
      NoTests(path, dent, is_dir))

def NoTestsNorFIPSFragments(path, dent, is_dir):
  return (NoTests(path, dent, is_dir) and
      (is_dir or not OnlyFIPSFragments(path, dent, is_dir)))

def NoTests(path, dent, is_dir):
  """Filter function that can be passed to FindCFiles in order to remove test
  sources."""
  if is_dir:
    return dent != 'test'
  return 'test.' not in dent


def OnlyTests(path, dent, is_dir):
  """Filter function that can be passed to FindCFiles in order to remove
  non-test sources."""
  if is_dir:
    return dent != 'test'
  return '_test.' in dent


def AllFiles(path, dent, is_dir):
  """Filter function that can be passed to FindCFiles in order to include all
  sources."""
  return True


def NoTestRunnerFiles(path, dent, is_dir):
  """Filter function that can be passed to FindCFiles or FindHeaderFiles in
  order to exclude test runner files."""
  # NOTE(martinkr): This prevents .h/.cc files in src/ssl/test/runner, which
  # are in their own subpackage, from being included in boringssl/BUILD files.
  return not is_dir or dent != 'runner'


def NotGTestSupport(path, dent, is_dir):
  return 'gtest' not in dent and 'abi_test' not in dent


def SSLHeaderFiles(path, dent, is_dir):
  return dent in ['ssl.h', 'tls1.h', 'ssl23.h', 'ssl3.h', 'dtls1.h', 'srtp.h']


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


def FindHeaderFiles(directory, filter_func):
  """Recurses through directory and returns a list of paths to all the header files that pass filter_func."""
  hfiles = []

  for (path, dirnames, filenames) in os.walk(directory):
    for filename in filenames:
      if not filename.endswith('.h'):
        continue
      if not filter_func(path, filename, False):
        continue
      hfiles.append(os.path.join(path, filename))

      for (i, dirname) in enumerate(dirnames):
        if not filter_func(path, dirname, True):
          del dirnames[i]

  hfiles.sort()
  return hfiles


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
      ['perl', input_filename, perlasm_style] + extra_args + [output_filename])


def ArchForAsmFilename(filename):
  """Returns the architectures that a given asm file should be compiled for
  based on substrings in the filename."""

  if 'x86_64' in filename or 'avx2' in filename:
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
  asmfiles = {}

  for osarch in OS_ARCH_COMBOS:
    (osname, arch, perlasm_style, extra_args, asm_ext) = osarch
    key = (osname, arch)
    outDir = os.path.join(DEST_DIR, ('%s-%s' % key))

    for perlasm in perlasms:
      filename = os.path.basename(perlasm['input'])
      output = perlasm['output']
      output = os.path.relpath(os.path.join(outDir, output), DEST_DIR)
      if output.endswith('-armx.${ASM_EXT}'):
        output = output.replace('-armx',
                                '-armx64' if arch == 'aarch64' else '-armx32')
      output = output.replace('${ASM_EXT}', asm_ext)

      if arch in ArchForAsmFilename(filename):
        PerlAsm(os.path.join(DEST_DIR, output), perlasm['input'], perlasm_style,
                perlasm['extra_args'] + extra_args)
        asmfiles.setdefault(key, []).append(output)

  for (key, non_perl_asm_files) in NON_PERL_FILES.items():
    asmfiles.setdefault(key, []).extend(non_perl_asm_files)

  for files in asmfiles.values():
    files.sort()

  return asmfiles


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


def main():
  cmake = ExtractVariablesFromCMakeFile(os.path.join(SRC_DIR, 'sources.cmake'))
  crypto_c_files = (FindCFiles(os.path.join(SRC_DIR, 'crypto'), NoTestsNorFIPSFragments) +
                    FindCFiles(os.path.join(SRC_DIR, 'third_party', 'fiat'), NoTestsNorFIPSFragments))
  fips_fragments = FindCFiles(os.path.join(SRC_DIR, 'crypto', 'fipsmodule'), OnlyFIPSFragments)
  ssl_source_files = FindCFiles(os.path.join(SRC_DIR, 'ssl'), NoTests)
  tool_c_files = FindCFiles(os.path.join(SRC_DIR, 'tool'), NoTests)
  tool_h_files = FindHeaderFiles(os.path.join(SRC_DIR, 'tool'), AllFiles)

  # BCM shared library C files
  bcm_crypto_c_files = [
      os.path.join(SRC_DIR, 'crypto', 'fipsmodule', 'bcm.c')
  ]

  # Generate err_data.c
  if not os.path.isdir(DEST_DIR):
    os.makedirs(DEST_DIR)

  with open(os.path.join(DEST_DIR, 'err_data.c'), 'w+') as err_data:
    subprocess.check_call(['go', 'run', 'err_data_generate.go'],
                          cwd=os.path.join(SRC_DIR, 'crypto', 'err'),
                          stdout=err_data)

  crypto_c_files.append('err_data.c')
  crypto_c_files.sort()

  test_support_c_files = FindCFiles(os.path.join(SRC_DIR, 'crypto', 'test'),
                                    NotGTestSupport)
  test_support_h_files = (
      FindHeaderFiles(os.path.join(SRC_DIR, 'crypto', 'test'), AllFiles) +
      FindHeaderFiles(os.path.join(SRC_DIR, 'ssl', 'test'), NoTestRunnerFiles))

  crypto_test_files = []

  # Generate crypto_test_data.cc
  with open(os.path.join(DEST_DIR, 'crypto_test_data.cc'), 'w+') as out:
    subprocess.check_call(
        ['go', 'run', 'util/embed_test_data.go'] + cmake['CRYPTO_TEST_DATA'],
        cwd=SRC_DIR,
        stdout=out)
  crypto_test_files += ['crypto_test_data.cc']

  crypto_test_files += FindCFiles(os.path.join(SRC_DIR, 'crypto'), OnlyTests)
  crypto_test_files += [
      os.path.join(SRC_DIR, 'crypto/test/abi_test.cc'),
      os.path.join(SRC_DIR, 'crypto/test/file_test_gtest.cc'),
      os.path.join(SRC_DIR, 'crypto/test/gtest_main.cc'),
  ]
  # urandom_test.cc is in a separate binary so that it can be test PRNG
  # initialisation.
  crypto_test_files = [
      file for file in crypto_test_files
      if not file.endswith('/urandom_test.cc')
  ]
  crypto_test_files.sort()

  ssl_test_files = FindCFiles(os.path.join(SRC_DIR, 'ssl'), OnlyTests)
  ssl_test_files += [
      os.path.join(SRC_DIR, 'crypto/test/abi_test.cc'),
      os.path.join(SRC_DIR, 'crypto/test/gtest_main.cc'),
  ]
  ssl_test_files.sort()

  urandom_test_files = [
      os.path.join(SRC_DIR, "crypto/fipsmodule/rand/urandom_test.cc"),
  ]

  fuzz_c_files = FindCFiles(os.path.join(SRC_DIR, 'fuzz'), NoTests)

  ssl_h_files = FindHeaderFiles(os.path.join(SRC_DIR, 'include', 'openssl'),
                                SSLHeaderFiles)

  def NotSSLHeaderFiles(path, filename, is_dir):
    return not SSLHeaderFiles(path, filename, is_dir)
  crypto_h_files = FindHeaderFiles(os.path.join(SRC_DIR, 'include', 'openssl'),
                                   NotSSLHeaderFiles)

  ssl_internal_h_files = FindHeaderFiles(os.path.join(SRC_DIR, 'ssl'), NoTests)
  crypto_internal_h_files = (
      FindHeaderFiles(os.path.join(SRC_DIR, 'crypto'), NoTests) +
      FindHeaderFiles(os.path.join(SRC_DIR, 'third_party', 'fiat'), NoTests))

  files = {
      'bcm_crypto': bcm_crypto_c_files,
      'crypto': crypto_c_files,
      'crypto_headers': crypto_h_files,
      'crypto_internal_headers': crypto_internal_h_files,
      'crypto_test': crypto_test_files,
      'crypto_test_data': sorted(os.path.join(SRC_DIR, x) for x in cmake['CRYPTO_TEST_DATA']),
      'fips_fragments': fips_fragments,
      'fuzz': fuzz_c_files,
      'ssl': ssl_source_files,
      'ssl_headers': ssl_h_files,
      'ssl_internal_headers': ssl_internal_h_files,
      'ssl_test': ssl_test_files,
      'tool': tool_c_files,
      'tool_headers': tool_h_files,
      'test_support': test_support_c_files,
      'test_support_headers': test_support_h_files,
      'urandom_test': urandom_test_files,
  }

  asm_outputs = sorted(WriteAsmFiles(ReadPerlAsmOperations()).items())

  return 0


if __name__ == '__main__':
  usage = '''%prog
      
  This script generates intermediate build files for CMake builds without the need
  to install Go or Perl as a dependency. These files are output to the |generated-src| 
  directory and are used by the top-level CMakeLists.txt for AWS-LC if these depedencies 
  are not found.
  '''

  parser = optparse.OptionParser(usage=usage)
  options, args = parser.parse_args(sys.argv[1:])

  SRC_DIR = os.getcwd()
  DEST_DIR = os.path.relpath('generated-src', os.getcwd())

  # NON_PERL_FILES enumerates assembly files that are not processed by the
  # perlasm system.
  NON_PERL_FILES = {
      ('linux', 'arm'): [
          os.path.relpath(os.path.join(SRC_DIR, "crypto/curve25519/asm/x25519-asm-arm.S"), DEST_DIR),
          os.path.relpath(os.path.join(SRC_DIR, "crypto/poly1305/asm/poly1305_asm_arm.S"), DEST_DIR),
      ],
      ('linux', 'x86_64'): [
          os.path.relpath(os.path.join(SRC_DIR, "crypto/hrss/asm/poly_rq_mul.S"), DEST_DIR),
      ],
  }

  sys.exit(main())
