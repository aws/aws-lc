# Install script for directory: /home/milaaws/Desktop/HPKE_SIKE/aws-lc-PQhpke/aws-lc

# Set the install prefix
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
  set(CMAKE_INSTALL_PREFIX "/home/milaaws/Desktop/HPKE_SIKE/aws-lc-PQhpke/aws-lc/aws-lc-install")
endif()
string(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set the install configuration name.
if(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)
  if(BUILD_TYPE)
    string(REGEX REPLACE "^[^A-Za-z0-9_]+" ""
           CMAKE_INSTALL_CONFIG_NAME "${BUILD_TYPE}")
  else()
    set(CMAKE_INSTALL_CONFIG_NAME "RefWithDebInfo")
  endif()
  message(STATUS "Install configuration: \"${CMAKE_INSTALL_CONFIG_NAME}\"")
endif()

# Set the component getting installed.
if(NOT CMAKE_INSTALL_COMPONENT)
  if(COMPONENT)
    message(STATUS "Install component: \"${COMPONENT}\"")
    set(CMAKE_INSTALL_COMPONENT "${COMPONENT}")
  else()
    set(CMAKE_INSTALL_COMPONENT)
  endif()
endif()

# Install shared libraries without execute permission?
if(NOT DEFINED CMAKE_INSTALL_SO_NO_EXE)
  set(CMAKE_INSTALL_SO_NO_EXE "1")
endif()

# Is this installation the result of a crosscompile?
if(NOT DEFINED CMAKE_CROSSCOMPILING)
  set(CMAKE_CROSSCOMPILING "FALSE")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xDevelopmentx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include" TYPE DIRECTORY FILES "/home/milaaws/Desktop/HPKE_SIKE/aws-lc-PQhpke/aws-lc/include/openssl")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xDevelopmentx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/AWSLC/cmake" TYPE FILE FILES "/home/milaaws/Desktop/HPKE_SIKE/aws-lc-PQhpke/aws-lc/aws-lc-build/awslc-config.cmake")
endif()

if(NOT CMAKE_INSTALL_LOCAL_ONLY)
  # Include the install script for each subdirectory.
  include("/home/milaaws/Desktop/HPKE_SIKE/aws-lc-PQhpke/aws-lc/aws-lc-build/crypto/cmake_install.cmake")
  include("/home/milaaws/Desktop/HPKE_SIKE/aws-lc-PQhpke/aws-lc/aws-lc-build/ssl/cmake_install.cmake")
  include("/home/milaaws/Desktop/HPKE_SIKE/aws-lc-PQhpke/aws-lc/aws-lc-build/tool/cmake_install.cmake")
  include("/home/milaaws/Desktop/HPKE_SIKE/aws-lc-PQhpke/aws-lc/aws-lc-build/decrepit/cmake_install.cmake")
  include("/home/milaaws/Desktop/HPKE_SIKE/aws-lc-PQhpke/aws-lc/aws-lc-build/util/fipstools/cavp/cmake_install.cmake")
  include("/home/milaaws/Desktop/HPKE_SIKE/aws-lc-PQhpke/aws-lc/aws-lc-build/util/fipstools/acvp/modulewrapper/cmake_install.cmake")

endif()

if(CMAKE_INSTALL_COMPONENT)
  set(CMAKE_INSTALL_MANIFEST "install_manifest_${CMAKE_INSTALL_COMPONENT}.txt")
else()
  set(CMAKE_INSTALL_MANIFEST "install_manifest.txt")
endif()

string(REPLACE ";" "\n" CMAKE_INSTALL_MANIFEST_CONTENT
       "${CMAKE_INSTALL_MANIFEST_FILES}")
file(WRITE "/home/milaaws/Desktop/HPKE_SIKE/aws-lc-PQhpke/aws-lc/aws-lc-build/${CMAKE_INSTALL_MANIFEST}"
     "${CMAKE_INSTALL_MANIFEST_CONTENT}")
