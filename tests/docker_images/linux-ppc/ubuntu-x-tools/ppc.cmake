# Specify the target system
set(CMAKE_SYSTEM_NAME Linux)
set(CMAKE_SYSTEM_PROCESSOR ppc)

# Specify the cross-compiler
set(CMAKE_C_COMPILER /powerpc-unknown-linux-gnu/bin/powerpc-unknown-linux-gnu-gcc)
set(CMAKE_CXX_COMPILER /powerpc-unknown-linux-gnu/bin/powerpc-unknown-linux-gnu-g++)

# Specify the sysroot for the target system
set(CMAKE_SYSROOT /powerpc-unknown-linux-gnu/powerpc-unknown-linux-gnu/sysroot)
set(CMAKE_GENERATOR Ninja)
