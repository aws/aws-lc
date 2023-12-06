# Specify the target system
set(CMAKE_SYSTEM_NAME Linux)
set(CMAKE_SYSTEM_PROCESSOR loongarch64)

# Specify the cross-compiler
set(CMAKE_C_COMPILER /loongarch64-unknown-linux-gnu/bin/loongarch64-unknown-linux-gnu-gcc)
set(CMAKE_CXX_COMPILER /loongarch64-unknown-linux-gnu/bin/loongarch64-unknown-linux-gnu-g++)

# Specify the sysroot for the target system
set(CMAKE_SYSROOT /loongarch64-unknown-linux-gnu/loongarch64-unknown-linux-gnu/sysroot)
set(CMAKE_GENERATOR Ninja)
