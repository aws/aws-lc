#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>

#define DEBUG 0

// regs[0 ~ 31]:  X registers
// regs[32 + 2*i]: Qi.d[0]
// regs[32 + 2*i+1]: Qi.d[1]
// regs[96..127]: [SP,...SP+255]

#define STATESIZE 128
static uint64_t regs[STATESIZE];

extern uint64_t harness(uint64_t *regfile);

void print_regs()
{ uint64_t i;
  for (i = 0; i < 32; ++i)
    printf("   %sX%"PRId64" = 0x%016"PRIx64"\n",((i<10)?" ":""),i,regs[i]);
  for (i = 0; i < 32; ++i)
    printf("   %sQ%"PRId64".{d[0], d[1]} = { 0x%016"PRIx64", 0x%016"PRIx64" }\n",((i<10)?" ":""),i,regs[32+i*2],regs[32+i*2+1]);
  for (i = 0; i < 32; ++i)
    printf("SP[%"PRId64"] = 0x%016"PRIx64"\n",i,regs[96+i]);
}

int main(int argc, char *argv[])
{ uint64_t retval, i;

  for (i = 1; i < argc && i <= STATESIZE; ++i)
    regs[i-1] = strtoul(argv[i],NULL,0);

  if (DEBUG)
   { printf("About to call harness with these arguments\n");
     print_regs();
   }

  retval = harness(regs);

  if (DEBUG)
   { printf("Called it and got %"PRIu64"\n",retval);
     print_regs();
   }
  else
   { for (i = 0; i < STATESIZE; ++i) printf("%"PRIu64" ",regs[i]);
     printf("\n");
   }

  return retval;
}
