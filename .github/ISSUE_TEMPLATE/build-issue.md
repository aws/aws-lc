---
name: AWS-LC Build Issue
about: Template
title: ''
labels: ''
assignees: ''

---

### Problem:

A short description of the problem you are facing. Please include any build output, reproduction steps and environment(e.g. [Docker image](https://github.com/aws/aws-lc/blame/e7413d237bb60bf639e78aa43ff3c1b1783f0712/tests/ci/docker_images/linux-x86/ubuntu-20.04_base/Dockerfile)).

#### Relevant details
AWS-LC commit: (6b1bce0...)

System information: for linux, below info can be collected by running `uname -srvmp`
 * CPU architecture: (x86, x86-64, ARMv7...)  
 * CPU name: (Xeon Platinum 8000, AMD EPYC 7000...)  
 * OS: (Ubuntu 20.04, Windows Server 2019...)  

Build log: 
 * The log tells compiler and version. It's available when building awslc with CMake.
```text
# Sample of build log
+ cmake -DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release -GNinja ../
-- The C compiler identification is GNU 7.5.0
-- Check for working C compiler: /usr/bin/gcc-7
-- Check for working C compiler: /usr/bin/gcc-7 -- works
-- Detecting C compiler ABI info
-- Detecting C compiler ABI info - done
-- Detecting C compile features
-- Detecting C compile features - done
-- The CXX compiler identification is GNU 7.5.0
-- Check for working CXX compiler: /usr/bin/g++-7
-- Check for working CXX compiler: /usr/bin/g++-7 -- works
-- Detecting CXX compiler ABI info
-- Detecting CXX compiler ABI info - done
-- Detecting CXX compile features
-- Detecting CXX compile features - done
-- Found Perl: /usr/bin/perl (found version "5.30.0") 
-- Checking for module 'libunwind-generic'
--   Found libunwind-generic, version 1.21
-- The ASM compiler identification is GNU
-- Found assembler: /usr/bin/gcc-7
-- Configuring done
-- Generating done
```
