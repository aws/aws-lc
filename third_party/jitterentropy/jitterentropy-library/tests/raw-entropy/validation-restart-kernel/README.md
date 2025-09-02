# Validation of Raw Entropy Data Restart Test

This validation tool processes the restart raw entropy data compliant to
SP800-90B section 3.1.4.

Each restart must be recorded in a single file where each raw entropy
value is stored on one line.

## Prerequisites

To execute the testing, you need:

	* NIST SP800-90B tool from:
		https://github.com/usnistgov/SP800-90B_EntropyAssessment

	* Obtain the sample data recorded on the target platforms

	* Configure processdata.sh with proper parameter values


### Parameters of processdata.sh

ENTROPYDATA_DIR: Location of the sample data files (with .data extension)

RESULTS_DIR: Location for the interim data bit streams and results.

LOGFILE: Name of the log file. The default is $RESULTS_DIR/processdata.log.

EATOOL: Path of the program used from the Entropy Assessment restart tool
(usually, ea_restart).

BUILD_EXTRACT: Indicates whether the script will build the extractlsb program.
The default is "yes".

MASK_LIST: Indicates the extraction method from each sample item. You can
indicate one or more methods; the script will generate one bit stream data
file for each extraction method. See below for a more detailed explanation.

SAMPLES: the number of samples (time deltas) that will be extracted from the
data. The default is 1000, as specified in SP800-90B.

RESTARTS: the number of test runs to be concatenated. The default is 1000, as
specified in SP 800-90B Each test run should be stored in a distinct file, from
jent_raw_noise_restart.00000.data to jent_raw_noise_restart.00999.data.

## Conclusion

The conclusion you have to draw is the following: To generate a 256 bit block,
the Jitter RNG obtains 256 time deltas (one time delta per bit at least, unless
the Jitter RNG performs oversampling). So, if you obtain a result that the
minimum entropy is more than 1 bit of entropy (per time delta), the one block
of 64 data bits is believed to have (close to) 64 bits of entropy. Otherwise it
will have relatively less entropy.

Please note that the minimum collision entropy value for 8 bits may be smaller
than the 4 bit values due to the inclusion of leading zeros. This, however is
a data processing problem that should be considered when drawing conclusions.
One can see the effect of these leading zeros by compressing the 4 bit and
8 bit data streams. Whereas the 4 bit data stream may not be compressable,
the 8 bit data stream may be compressed

This may also occur when the least significant bits in the time delta do not
change.  You need to refine the extraction method to reach to the right
calculation.


[1] https://github.com/usnistgov/SP800-90B_EntropyAssessment
