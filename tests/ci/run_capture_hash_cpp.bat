@echo off
setlocal enabledelayedexpansion

REM Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
REM SPDX-License-Identifier: Apache-2.0 OR ISC
REM Adapted from tests/ci/run_windows_tests.bat

echo Running capture_hash.cpp tests...

REM Setup environment (from run_windows_tests.bat)
set SRC_ROOT=%cd%
set BUILD_DIR=%SRC_ROOT%\test_build_dir

REM Setup Visual Studio environment - using same pattern as run_windows_tests.bat
REM We'll assume GitHub Actions provides the right VS environment, but check anyway
cl >nul 2>&1
if !errorlevel! neq 0 (
    echo Error: Visual Studio build tools not available
    exit /b 1
)

REM Build with our specific configuration (adapted from existing :build function)
call :build RelWithDebInfo "-DFIPS=1 -DBUILD_SHARED_LIBS=1 -DUSE_CPP_INJECT_HASH=ON" || goto error

cd /d "%BUILD_DIR%"

REM Initialize error counter
set ERRORS=0

echo.
echo TESTING CAPTURE_HASH.CPP WITH EDGE CASES...

REM Test 1: No arguments (should fail)
echo Running test: No arguments test
util\fipstools\inject_hash_cpp\capture_hash_cpp.exe >nul 2>&1
if !errorlevel! == 0 (
    echo Test 'No arguments test' was expected to fail but succeeded
    set /a ERRORS+=1
) else (
    echo Test 'No arguments test' failed as expected
)

REM Test 2: Invalid file (should fail)  
echo Running test: Invalid file test
util\fipstools\inject_hash_cpp\capture_hash_cpp.exe -in-executable nonexistent.exe >nul 2>&1
if !errorlevel! == 0 (
    echo Test 'Invalid file test' was expected to fail but succeeded
    set /a ERRORS+=1
) else (
    echo Test 'Invalid file test' failed as expected
)

REM Test 3: FIPS integrity sanity check(should succeed)
echo Running test: FIPS integrity sanity check
crypto\crypto_test.exe >nul 2>&1
if !errorlevel! neq 0 (
    echo Test 'FIPS integrity sanity check' failed - FIPS module has integrity issues
    set /a ERRORS+=1
) else (
    echo Test 'FIPS integrity sanity check' passed - FIPS module integrity OK
)

echo.
echo === Summary ===
echo Total errors: !ERRORS!

if !ERRORS! gtr 0 (
    echo One or more tests failed
    exit /b 1
) else (
    echo All tests passed
    exit /b 0
)

REM Build function copied from run_windows_tests.bat
REM Note: The build function is intentionally duplicated from run_windows_tests.bat
REM       as Windows batch files don't support function sharing like bash scripts.
REM       This keeps the script self-contained and more reliable.
:build
@echo on
@echo LOG: %date%-%time% %1 %2 build started with cmake generation
cd %SRC_ROOT%
rmdir /s /q %BUILD_DIR%
mkdir %BUILD_DIR%
cd %BUILD_DIR%

cmake -GNinja -DCMAKE_BUILD_TYPE=%~1 %~2 %SRC_ROOT% || goto error

@echo LOG: %date%-%time% %1 %2 cmake generation complete, starting build
ninja || goto error
@echo LOG: %date%-%time% %1 %2 build complete
@echo off
exit /b 0

:error
echo Failed with error #%errorlevel%.
exit /b 1
