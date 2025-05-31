# AWS-LC Style Guide
AWS-LC followings the #BoringSSL-Style-Guide conventions unless specified otherwise here.

## Documentation
This section provides a brief overview of how to use [Doxygen](https://www.doxygen.nl/manual/index.html) as well as the standard convensions we follow in our code.

### General Syntax Guidelines

#### Use C-Style Blocks
Use the double asterisk C-style Doxygen blocks (`/** */`) instead of C++ lines (`///`) or comment block formats. The starting symbol `/**` and closing symbol `*/` should be on their own lines:
```C
/**
 * ... Documentation ...
 */
```
except when closing a member group:
```C
/** @} Member Group Name */
```

#### Use `@` for Commands
Use `@` to prefix all commands instead of `\`.

#### Explicitly use the `@brief` command.
Instead of relying on Doxygen to generate a brief description, explicitly use the `@brief` command. For readability, this should end with a period and if there's further documentation, an empty line should follow the command in the block.
```C
/**
 * @brief A short description.
 */

/**
 * @brief A short description followed by details.
 * 
 * ... More documentation ...
 */
```

#### Explicitly use the `@details` command.
Instead of relying on Doxygen to decide what is the details section, the `@details` command should be used. The command should be on its own line.
```C
/**
 * @details
 * ... Detailed information...
 */
```

#### Use backticks around inline code
When including code inline, to get typewriter font, use backticks instead of the `@c` command. This should also be used when referncing the symbols being documented.
```C
/**
 * @details
 * `this_function` encodes...
 */
int this_function()
```

#### Use `@code`/`@endcode` for full lines of source code
If your documentation includes full lines of code (such as examples), surround the line(s) by `@code`/`@endcode` for syntax highlighting and automatic generation of links to documentation for the symbols used. For readability, empty lines should surround the block and the commands should be on their own lines.
```C
/**
 * @details
 * ... Documentation ...
 * 
 * @code
 * uint8_t dst = allocate(max_len);
 * size_t len = encode_bytes(dst, src, src_len);
 * @endcode
 */
```

### Formatting Regular Text

#### Use Underscores for Italic Text
When documentation should be in italics, use the Markdown underscore syntax.
```
Roman text _italic text_ Roman text
```

#### Use Double Asterisks for Bold Text
When documentation should be in bold, use the Markdown double asterisk syntax.
```
Roman text **bold text** Roman text
```

#### Lists
For unordered lists, use `*` for each item, not `-` or `+`. For orded lists, use `1.` for each item. Do not use other numbers, allow them to be generated automatically. Nested lists should be indented by two spaces.
```
1. First enumerated point (level 1)
1. Second enuemrated point (level 1)
  * First unordered point (level 2)
  * Second unordered point (level 2)
1. Third enumerated point (level 1)
```

### All public headers must have API documentation
All public headers (files in the `include` directory generally) must have the appropriate documentation. Besides documentation on the exported symbols, the file should have at least a brief description of its purpose.
```C
/**
 * @file 
 * @brief A short description.
 * 
 * @details
 * A longer, optional description of the file's purpose.
 */
```
In general, `@file` should not include the (optional name parameter)[https://www.doxygen.nl/manual/commands.html#cmdfile].

# BoringSSL Style Guide

BoringSSL usually follows the
[Google C++ style guide](https://google.github.io/styleguide/cppguide.html),
The rest of this document describes differences and clarifications on
top of the base guide.


## Legacy code

As a derivative of OpenSSL, BoringSSL contains a lot of legacy code that
does not follow this style guide. Particularly where public API is
concerned, balance consistency within a module with the benefits of a
given rule. Module-wide deviations on naming should be respected while
integer and return value conventions take precedence over consistency.

Modules from OpenSSL's legacy ASN.1 and X.509 stack are retained for
compatibility and left largely unmodified. To ease importing patches from
upstream, they match OpenSSL's new indentation style. For Emacs,
`doc/openssl-c-indent.el` from OpenSSL may be helpful in this.


## Language

The majority of the project is in C, so C++-specific rules in the
Google style guide do not apply. Support for C99 features depends on
our target platforms. Typically, Chromium's target MSVC is the most
restrictive.

Variable declarations in the middle of a function or inside a `for` loop are
allowed and preferred where possible. Note that the common `goto err` cleanup
pattern requires lifting some variable declarations.

Comments should be `// C99-style` for consistency with C++.

When declaring pointer types, `*` should be placed next to the variable name,
not the type. So

    uint8_t *ptr;

not

    uint8_t* ptr;

Rather than `malloc()` and `free()`, use the wrappers `OPENSSL_malloc()`
and `OPENSSL_free()`. Use the standard C `assert()` function freely.

Use the following wrappers, found in `crypto/internal.h` instead of the
corresponding C standard library functions. They behave the same but avoid
confusing undefined behavior.

* `OPENSSL_memchr`
* `OPENSSL_memcmp`
* `OPENSSL_memcpy`
* `OPENSSL_memmove`
* `OPENSSL_memset`

For new constants, prefer enums when the values are sequential and typed
constants for flags. If adding values to an existing set of `#define`s,
continue with `#define`.


## libssl

libssl was originally written in C but is being incrementally rewritten in
C++11. As of writing, much of the style matches our C conventions rather than
Google C++. Additionally, libssl on Linux currently may not depend on the C++
runtime. See the C++ utilities in `ssl/internal.h` for replacements for
problematic C++ constructs. The `util/check_imported_libraries.go` script may be
used with a shared library build to check if a new construct is okay.

If unsure, match surrounding code. Discrepancies between it and Google C++ style
will be fixed over time.


## Formatting

Single-statement blocks are not allowed. All conditions and loops must
use braces:

    if (foo) {
      do_something();
    }

not

    if (foo)
      do_something();


## Integers

Prefer using explicitly-sized integers where appropriate rather than
generic C ones. For instance, to represent a byte, use `uint8_t`, not
`unsigned char`. Likewise, represent a two-byte field as `uint16_t`, not
`unsigned short`.

Sizes are represented as `size_t`.

Within a struct that is retained across the lifetime of an SSL
connection, if bounds of a size are known and it's easy, use a smaller
integer type like `uint8_t`. This is a "free" connection footprint
optimization for servers. Don't make code significantly more complex for
it, and do still check the bounds when passing in and out of the
struct. This narrowing should not propagate to local variables and
function parameters.

When doing arithmetic, account for overflow conditions.

Except with platform APIs, do not use `ssize_t`. MSVC lacks it, and
prefer out-of-band error signaling for `size_t` (see Return values).


## Naming

Follow Google naming conventions in C++ files. In C files, use the
following naming conventions for consistency with existing OpenSSL and C
styles:

Define structs with typedef named `TYPE_NAME`. The corresponding struct
should be named `struct type_name_st`.

Name public functions as `MODULE_function_name`, unless the module
already uses a different naming scheme for legacy reasons. The module
name should be a type name if the function is a method of a particular
type.

Some types are allocated within the library while others are initialized
into a struct allocated by the caller, often on the stack. Name these
functions `TYPE_NAME_new`/`TYPE_NAME_free` and
`TYPE_NAME_init`/`TYPE_NAME_cleanup`, respectively. All `TYPE_NAME_free`
functions must do nothing on `NULL` input.

If a variable is the length of a pointer value, it has the suffix
`_len`. An output parameter is named `out` or has an `out_` prefix. For
instance, For instance:

    uint8_t *out,
    size_t *out_len,
    const uint8_t *in,
    size_t in_len,

Name public headers like `include/openssl/evp.h` with header guards like
`OPENSSL_HEADER_EVP_H`. Name internal headers like
`crypto/ec/internal.h` with header guards like
`OPENSSL_HEADER_EC_INTERNAL_H`.

Name enums like `enum unix_hacker_t`. For instance:

    enum should_free_handshake_buffer_t {
      free_handshake_buffer,
      dont_free_handshake_buffer,
    };


## Return values

As even `malloc` may fail in BoringSSL, the vast majority of functions
will have a failure case. Functions should return `int` with one on
success and zero on error. Do not overload the return value to both
signal success/failure and output an integer. For example:

    OPENSSL_EXPORT int CBS_get_u16(CBS *cbs, uint16_t *out);

If a function needs more than a true/false result code, define an enum
rather than arbitrarily assigning meaning to int values.

If a function outputs a pointer to an object on success and there are no
other outputs, return the pointer directly and `NULL` on error.


## Parameters

Where not constrained by legacy code, parameter order should be:

1. context parameters
2. output parameters
3. input parameters

For example,

    /* CBB_add_asn sets |*out_contents| to a |CBB| into which the contents of an
     * ASN.1 object can be written. The |tag| argument will be used as the tag for
     * the object. It returns one on success or zero on error. */
    OPENSSL_EXPORT int CBB_add_asn1(CBB *cbb, CBB *out_contents, unsigned tag);


## Build logic

BoringSSL is used by many projects with many different build tools.
Reimplementing and maintaining build logic in each downstream build is
cumbersome, so build logic should be avoided where possible. Platform-specific
files should be excluded by wrapping the contents in `#ifdef`s, rather than
computing platform-specific file lists. Generated source files such as perlasm
and `err_data.c` may be used in the standalone CMake build but, for downstream
builds, they should be pre-generated in `generate_build_files.py`.
