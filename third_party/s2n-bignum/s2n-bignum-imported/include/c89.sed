# Delete up to the first line containing Add (i.e. scrub banners)

/Add/,$!d

# Eliminate static qualifiers in function arguments

s/S2N_BIGNUM_STATIC //g

# Convert BCPL/C++ comments to original C style

s!^// *(.*)!/* \1 */!

# If we want to remove const qualifiers.
# However, we don't since this is in C89
# s!const !!g
