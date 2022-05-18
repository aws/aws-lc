#ifdef __APPLE__
#define S2N_ASM_HIDDEN(name) .private_extern name
#else
#define S2N_ASM_HIDDEN(name) .hidden name
#endif
