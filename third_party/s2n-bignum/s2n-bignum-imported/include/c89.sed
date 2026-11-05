# Delete banner and S2N_BIGNUM_STATIC preprocessor guards (through first #endif)

1,/^#endif$/d

# Drop leading blank lines left after the guard removal

/./,$!d

# Eliminate static qualifiers in function arguments

s/S2N_BIGNUM_STATIC //g

# Convert BCPL/C++ comments to original C style

s!^// *(.*)!/* \1 */!

# If we want to remove const qualifiers.
# However, we don't since this is in C89
# s!const !!g
