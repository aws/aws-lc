## s2n-bignum

This is a collection of bignum arithmetic routines designed for crypto
applications. All routines are written in pure machine code, designed
to be callable from C with separate but API-compatible versions of
each function for 64-bit x86 (x86_64) and ARM (aarch64). Each routine
is written in a constant-time style to avoid timing side-channels, and
each function is accompanied by a machine-checked formal proof that
its mathematical result is correct, based on a formal model of the
underlying machine.

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.

