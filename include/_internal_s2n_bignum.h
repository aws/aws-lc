
#ifdef __APPLE__
#define S2N_BN_SYM_VISIBILITY_DIRECTIVE(name) .globl _##name
#ifdef S2N_BN_HIDE_SYMBOLS
#define S2N_BN_SYM_PRIVACY_DIRECTIVE(name) .private_extern _##name
#else
#define S2N_BN_SYM_PRIVACY_DIRECTIVE(name)  /* NO-OP: S2N_BN_SYM_PRIVACY_DIRECTIVE */
#endif
#define S2N_BN_SYMBOL(name) _##name
#else
#define S2N_BN_SYM_VISIBILITY_DIRECTIVE(name) .globl name
#ifdef S2N_BN_HIDE_SYMBOLS
#define S2N_BN_SYM_PRIVACY_DIRECTIVE(name) .hidden name
#else
#define S2N_BN_SYM_PRIVACY_DIRECTIVE(name)  /* NO-OP: S2N_BN_SYM_PRIVACY_DIRECTIVE */
#endif
#define S2N_BN_SYMBOL(name) name
#endif