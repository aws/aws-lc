// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/base.h>

#if defined(BORINGSSL_FIPS) && defined(OPENSSL_WINDOWS)
#include <stdio.h>
#include <windows.h>

extern void BORINGSSL_bcm_power_on_self_test(void);
extern void rand_thread_state_clear_all(void);

int WINAPI DllMain(
    HINSTANCE hinstDLL,  // handle to DLL module
    DWORD fdwReason,     // reason for calling function
    LPVOID lpReserved )  // reserved
{
  // Perform actions based on the reason for calling.
  switch( fdwReason )
  {
    case DLL_PROCESS_ATTACH:
      // Mimic the functionalilty provided by __attribute__((constructor))
      BORINGSSL_bcm_power_on_self_test();
      break;

    case DLL_THREAD_ATTACH:
      // No thread specific initialization is needed, all of the rand state is
      // lazily initialized
      break;

    case DLL_THREAD_DETACH:
      // No thread specific cleanup needed
      break;

    case DLL_PROCESS_DETACH:
      // Mimic the functionality provided by __attribute__((destructor))
      rand_thread_state_clear_all();
      break;
  }
  return 1;  // Successful DLL_PROCESS_ATTACH.
}

#endif
