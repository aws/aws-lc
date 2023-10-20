// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <windows.h>
#include <stdio.h>
#include <stdlib.h>


int main(int argc, char *argv[]) {

  char password[20];
  strcpy(password, "MySecretPassword");

  // Display the password before erasing it
  printf("Password before erasing: %s\n", password);

  // Securely erase the password from memory
  SecureZeroMemory(password, sizeof(password));

  // Display the password after erasing
  printf("Password after erasing: %s\n", password);

  fprintf(stdout, "PASS\n");
  fflush(stdout);
  return 0;
}
