# Specify the target system
set(CMAKE_SYSTEM_NAME Linux)
set(CMAKE_SYSTEM_PROCESSOR s390x)

# Specify the cross-compiler
set(CMAKE_C_COMPILER /s390x-ibm-linux-gnu/bin/s390x-ibm-linux-gnu-gcc)
set(CMAKE_CXX_COMPILER /s390x-ibm-linux-gnu/bin/s390x-ibm-linux-gnu-g++)

# Specify the sysroot for the target system
set(CMAKE_SYSROOT /s390x-ibm-linux-gnu/s390x-ibm-linux-gnu/sysroot)
set(CMAKE_GENERATOR Ninja)
