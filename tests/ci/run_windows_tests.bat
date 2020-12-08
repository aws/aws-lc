@echo on
set BUILD_DIR=%CODEBUILD_SRC_DIR%\test_build_dir
set INSTALL_DIR=%BUILD_DIR%\install


@rem %1 contains the path to the setup batch file for the version of of visual studio that was passed in from the build spec file.
@rem x64 comes from the architecture options https://docs.microsoft.com/en-us/cpp/build/building-on-the-command-line
call %1 x64 || goto error
SET
call :build_and_test Release "" || goto error

@rem call :build_and_test Release "-DOPENSSL_SMALL=1" || goto error
@rem The NO_ASM fails due to some missing 'dummy_chacha20_poly1305_asm'
@rem call :build_and_test Release "-DOPENSSL_NO_ASM=1" || goto error
@rem The SHARED_LIBS build fails due to go not being able to write some file
@rem call :build_and_test Release "-DBUILD_SHARED_LIBS=1" || goto error
@rem The debug build currently fails due to 1073741515 missing Dll call :build_and_test aws-lc Debug || goto error
@rem call :build_and_test Debug "" || goto error

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
cd %CODEBUILD_SRC_DIR%
rmdir /s /q %BUILD_DIR%
mkdir %BUILD_DIR%
mkdir %INSTALL_DIR%
cd %BUILD_DIR%

cmake -GNinja -DCMAKE_BUILD_TYPE=%~1 %~2 -DCMAKE_INSTALL_PREFIX="%INSTALL_DIR%" -DCMAKE_PREFIX_PATH="%INSTALL_DIR%" %CODEBUILD_SRC_DIR% || goto error

@echo  LOG: %date%-%time% %1 %2 cmake generation complete, starting build
ninja || goto error
exit /b 0


@rem Use the same parameters as build_and_test, this assumes the build is complete
:test
@echo on
@echo  LOG: %date%-%time% %1 %2 build finished, starting tests
ninja -C %BUILD_DIR% run_tests || goto error
@echo  LOG: %date%-%time% %1 %2 tests complete
exit /b %errorlevel%

:error
echo Failed with error #%errorlevel%.
type CMakeFiles\CMakeOutput.log
type CMakeFiles\CMakeError.log
exit /b 1
