## AT&T syntax versions

This directory contains AT&T syntax equivalents of the original Intel
syntax assembler files, generated automatically by a naive script and
subject to a sanity check that the object code doesn't change. All the
*/*.S files are generated ("make code"). Direct modification of these
files is not recommended.

        make code    --- Generate */*.S files, subject to sanity check
        make all     --- Generate */*.S and */*.o files with sanity check
        make clean   --- Delete object files
        make clobber --- Delete object files and generated code

For more on the two syntax variants see:

        https://en.wikipedia.org/wiki/X86_assembly_language#Syntax
