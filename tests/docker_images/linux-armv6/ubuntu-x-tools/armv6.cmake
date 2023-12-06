# Specify the target system
set(CMAKE_SYSTEM_NAME Linux)
set(CMAKE_SYSTEM_PROCESSOR armv6l)

# Specify the cross-compiler
set(CMAKE_C_COMPILER /armv6-unknown-linux-gnueabi/bin/armv6-unknown-linux-gnueabi-gcc)
set(CMAKE_CXX_COMPILER /armv6-unknown-linux-gnueabi/bin/armv6-unknown-linux-gnueabi-g++)

# Specify the sysroot for the target system
set(CMAKE_SYSROOT /armv6-unknown-linux-gnueabi/armv6-unknown-linux-gnueabi/sysroot)
set(CMAKE_GENERATOR Ninja)
