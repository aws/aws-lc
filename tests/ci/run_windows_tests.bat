@echo on
set SRC_ROOT=%cd%
set BUILD_DIR=%SRC_ROOT%\test_build_dir

@rem %1 contains the path to the setup batch file for the version of of visual studio that was passed in from the build spec file.
@rem %2 specifies the architecture option to build against: https://docs.microsoft.com/en-us/cpp/build/building-on-the-command-line
@rem %3 is to indicate running SDE simulation tests. If not set, SDE tests are not run.
set MSVC_PATH=%1
set ARCH_OPTION=%2
if "%~3"=="" ( set RUN_SDE=false ) else ( set RUN_SDE=%3 )
call %MSVC_PATH% %ARCH_OPTION% || goto error
SET

@echo on
if /i "%RUN_SDE%" == "false " (
	goto :run_basic_tests
) else if /i "%RUN_SDE%" == "true " (
	goto :run_sde_tests
) else (
	@rem Unrecognized option
	goto error
)
goto :EOF

:run_basic_tests
@rem Run the same builds as run_posix_tests.sh
@rem Check which version of MSVC we're building with: remove 14.0 from the path to the compiler and check if it matches the
@rem original string. MSVC 14 has an issue with a missing DLL that causes the debug unit tests to fail
if x%MSVC_PATH:14.0=%==x%MSVC_PATH% call :build_and_test Debug "" || goto error
call :build_and_test Release "" || goto error
call :build_and_test Release "-DOPENSSL_SMALL=1" || goto error
call :build_and_test Release "-DOPENSSL_NO_ASM=1" || goto error

@rem Windows has no equivalent of Linux's rpath so it can't find the built dlls from CMake. We also don't want to install our
@rem tests or copy them around so Windows can find it in the same directory. Instead just put the dll's location onto the path
set PATH=%BUILD_DIR%;%BUILD_DIR%\crypto;%BUILD_DIR%\ssl;%PATH%
call :build_and_test Release "-DBUILD_SHARED_LIBS=1" || goto error
call :build_and_test Release "-DBUILD_SHARED_LIBS=1 -DFIPS=1" || goto error
@rem For FIPS on Windows we also have a RelWithDebInfo build to generate debug symbols.
call :build_and_test RelWithDebInfo "-DBUILD_SHARED_LIBS=1 -DFIPS=1" || goto error
exit /b 0

:run_sde_tests
@rem Run and test the same dimensions as our Linux SDE tests.
call :build_and_test_with_sde Debug "" || goto error
call :build_and_test_with_sde Release "" || goto error
exit /b 0

@rem %1 is the build type (e.g. Release/Debug)
@rem %2 is the additional full CMake args
:build_and_test
@echo on
call :build %1 %2 || goto error
call :test %1 %2 || goto error
exit /b 0

@rem %1 is the build type (e.g. Release/Debug)
@rem %2 is the additional full CMake args
:build_and_test_with_sde
@echo on
call :build %1 %2 || goto error
call :test_with_sde %1 %2 || goto error
exit /b 0

@rem Use the same parameters as build_and_test
:build
@echo on
@echo  LOG: %date%-%time% %1 %2 build started with cmake generation started
cd %SRC_ROOT%
rmdir /s /q %BUILD_DIR%
mkdir %BUILD_DIR%
cd %BUILD_DIR%

cmake -GNinja -DCMAKE_BUILD_TYPE=%~1 %~2 %SRC_ROOT% || goto error

@echo  LOG: %date%-%time% %1 %2 cmake generation complete, starting build
ninja || goto error
exit /b 0

@rem Use the same parameters as build_and_test, this assumes the build is complete
:test
@echo on
@echo  LOG: %date%-%time% %1 %2 build finished, starting tests
ninja run_tests || goto error
@echo  LOG: %date%-%time% %1 %2 tests complete
exit /b %errorlevel%

@rem Runs the SDE simulator tests, this assumes the build is complete
:test_with_sde
@echo on
@echo  LOG: %date%-%time% %1 %2 build finished, starting tests with SDE
ninja run_tests_with_sde || goto error
@echo  LOG: %date%-%time% %1 %2 SDE tests complete
exit /b %errorlevel%

:error
echo Failed with error #%errorlevel%.
exit /b 1
