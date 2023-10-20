// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <stdio.h>
#include <stdlib.h>
#include <string.h>


int main(int argc, char *argv[]) {

  char password[20];
  strcpy(password, "MySecretPassword");

  printf("Password before erasing: %s\n", password);

  memset(password, 0, sizeof(password));

  printf("Password after erasing: %s\n", password);

  fprintf(stdout, "PASS\n");
  fflush(stdout);
  return 0;
}
