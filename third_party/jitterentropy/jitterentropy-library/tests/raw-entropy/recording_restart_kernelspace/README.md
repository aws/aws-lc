# Tests of Entropy during early boot

This test collects the first 1,001 entropy event values generated during boot
of the Linux kernel. The collection of raw entropy after reboot is compliant
to SP800-90B section 3.1.4.

The test infrastructure sets the Linux system up to reboot the system
some 1,000 times to collect these 1,001 event values.

# Test procedure

See boottime_test_record.sh.

The result is a matrix where on each line the 1,001 successive time stamps
of the interrupts for one boot operation are recorded.

The number of lines equals to the number of reboots.

# Test analysis

Copy the obtained output file into results and process the result by
invoking validation-restart-*/processdata.sh.
