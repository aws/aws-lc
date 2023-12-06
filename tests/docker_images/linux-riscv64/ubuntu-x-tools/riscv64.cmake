# Specify the target system
set(CMAKE_SYSTEM_NAME Linux)
set(CMAKE_SYSTEM_PROCESSOR riscv64)

# Specify the cross-compiler
set(CMAKE_C_COMPILER /riscv64-unknown-linux-gnu/bin/riscv64-unknown-linux-gnu-gcc)
set(CMAKE_CXX_COMPILER /riscv64-unknown-linux-gnu/bin/riscv64-unknown-linux-gnu-g++)

# Specify the sysroot for the target system
set(CMAKE_SYSROOT /riscv64-unknown-linux-gnu/riscv64-unknown-linux-gnu/sysroot)
set(CMAKE_GENERATOR Ninja)
