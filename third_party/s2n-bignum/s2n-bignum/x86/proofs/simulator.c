#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>

#define DEBUG 0

// regs[0..111]:  integer registers, YMMs, flags and small buffer in stack
//
//      RAX = regfile[0]
//      RCX = regfile[1]
//      RDX = regfile[2]
//      RBX = regfile[3]
//      OF:xx:xx:xx:SF:ZF:xx:AF:xx:PF:xx:CF = regfile[4] & 0xFF
//      RBP = regfile[5]
//      RSI = regfile[6]
//      RDI = regfile[7]
//       R8 = regfile[8]
//       R9 = regfile[9]
//      R10 = regfile[10]
//      R11 = regfile[11]
//      R12 = regfile[12]
//      R13 = regfile[13]
//      R14 = regfile[14]
//      R15 = regfile[15]
//      YMM0.d[0] = regfile[16]
//      YMM0.d[1] = regfile[17]
//      YMM0.d[2] = regfile[18]
//      YMM0.d[3] = regfile[19]
//      YMM1.d[0] = regfile[20]
//      ...
//      YMM15.d[2] = regfile[78]
//      YMM15.d[3] = regfile[79]
//      [SP,...,SP+255] = regfile[80...111]

#define STATESIZE 112
static uint64_t regs[STATESIZE];

extern uint64_t harness(uint64_t *regfile);

void print_regs()
{ uint64_t i;
  printf("   RAX = 0x%016"PRIx64"\n",regs[0]);
  printf("   RCX = 0x%016"PRIx64"\n",regs[1]);
  printf("   RDX = 0x%016"PRIx64"\n",regs[2]);
  printf("   RBX = 0x%016"PRIx64"\n",regs[3]);
  printf("   RBP = 0x%016"PRIx64"\n",regs[5]);
  printf("   RSI = 0x%016"PRIx64"\n",regs[6]);
  printf("   RDI = 0x%016"PRIx64"\n",regs[7]);
  printf("    R8 = 0x%016"PRIx64"\n",regs[8]);
  printf("    R9 = 0x%016"PRIx64"\n",regs[9]);
  printf("   R10 = 0x%016"PRIx64"\n",regs[10]);
  printf("   R11 = 0x%016"PRIx64"\n",regs[11]);
  printf("   R12 = 0x%016"PRIx64"\n",regs[12]);
  printf("   R13 = 0x%016"PRIx64"\n",regs[13]);
  printf("   R14 = 0x%016"PRIx64"\n",regs[14]);
  printf("   R15 = 0x%016"PRIx64"\n",regs[15]);
  printf("    OF = %d\n",(regs[4] & (1<<11)) != 0);
  printf("    SF = %d\n",(regs[4] & (1<<7)) != 0);
  printf("    ZF = %d\n",(regs[4] & (1<<6)) != 0);
  printf("    AF = %d\n",(regs[4] & (1<<4)) != 0);
  printf("    PF = %d\n",(regs[4] & (1<<2)) != 0);
  printf("    CF = %d\n",(regs[4] & (1<<0)) != 0);
  printf("  YMM0 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[19],regs[18],regs[17],regs[16]);
  printf("  YMM1 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[23],regs[22],regs[21],regs[20]);
  printf("  YMM2 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[27],regs[26],regs[25],regs[24]);
  printf("  YMM3 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[31],regs[30],regs[29],regs[28]);
  printf("  YMM4 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[35],regs[34],regs[33],regs[32]);
  printf("  YMM5 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[39],regs[38],regs[37],regs[36]);
  printf("  YMM6 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[43],regs[42],regs[41],regs[40]);
  printf("  YMM7 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[47],regs[46],regs[45],regs[44]);
  printf("  YMM8 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[51],regs[50],regs[49],regs[48]);
  printf("  YMM9 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[55],regs[54],regs[53],regs[52]);
  printf(" YMM10 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[59],regs[58],regs[57],regs[56]);
  printf(" YMM11 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[63],regs[62],regs[61],regs[60]);
  printf(" YMM12 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[67],regs[66],regs[65],regs[64]);
  printf(" YMM13 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[71],regs[70],regs[69],regs[68]);
  printf(" YMM14 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[75],regs[74],regs[73],regs[72]);
  printf(" YMM15 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[79],regs[78],regs[77],regs[76]);
  printf(" SP0 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[80],regs[81],regs[82],regs[83]);
  printf(" SP1 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[84],regs[85],regs[86],regs[87]);
  printf(" SP2 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[88],regs[89],regs[90],regs[91]);
  printf(" SP3 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[92],regs[93],regs[94],regs[95]);
  printf(" SP4 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[96],regs[97],regs[98],regs[99]);
  printf(" SP5 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[100],regs[101],regs[102],regs[103]);
  printf(" SP6 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[104],regs[105],regs[106],regs[107]);
  printf(" SP7 = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",regs[108],regs[109],regs[110],regs[111]);
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
