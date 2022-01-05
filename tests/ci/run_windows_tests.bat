@echo on
set SRC_ROOT=%cd%
set BUILD_DIR=%SRC_ROOT%\test_build_dir


@rem %1 contains the path to the setup batch file for the version of of visual studio that was passed in from the build spec file.
@rem x64 comes from the architecture options https://docs.microsoft.com/en-us/cpp/build/building-on-the-command-line
call %1 x64 || goto error
SET

@rem Run the same builds as run_posix_tests.sh
call :build_and_test Debug "" || goto error
call :build_and_test Release "" || goto error
call :build_and_test Release "-DOPENSSL_SMALL=1" || goto error
call :build_and_test Release "-DOPENSSL_NO_ASM=1" || goto error

@rem Windows has no equivalent of Linux's rpath so it can't find the built dlls from CMake. We also don't want to install our
@rem tests or copy them around so Windows can find it in the same directory. Instead just put the dll's location onto the path
set PATH=%BUILD_DIR%;%BUILD_DIR%\crypto;%BUILD_DIR%\ssl;%PATH%
call :build_and_test Release "-DBUILD_SHARED_LIBS=1" || goto error

goto :EOF

@rem %1 is the build type Release/Debug
@rem %2 is the additional full CMake args
:build_and_test
@echo on
call :build %1 %2 || goto error
call :test %1 %2 || goto error
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

:error
echo Failed with error #%errorlevel%.
exit /b 1
