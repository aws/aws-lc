# Specify the target system
set(CMAKE_SYSTEM_NAME Linux)
set(CMAKE_SYSTEM_PROCESSOR ppc64le)

# Specify the cross-compiler
set(CMAKE_C_COMPILER /powerpc64le-unknown-linux-gnu/bin/powerpc64le-unknown-linux-gnu-gcc)
set(CMAKE_CXX_COMPILER /powerpc64le-unknown-linux-gnu/bin/powerpc64le-unknown-linux-gnu-g++)

# Specify the sysroot for the target system
set(CMAKE_SYSROOT /powerpc64le-unknown-linux-gnu/powerpc64le-unknown-linux-gnu/sysroot)
set(CMAKE_GENERATOR Ninja)
