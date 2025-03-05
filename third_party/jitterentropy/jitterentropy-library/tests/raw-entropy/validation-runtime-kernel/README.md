# Validation of Raw Entropy Data - Kernel

This tool is used to calculate the minimum entropy values
compliant to SP800-90B for the gathered data.

The validation operation of the raw entropy data is invoked with the
processdata.sh script.

The sampling data from the recording operation must be post-processed. This is
because you need to determine which part of the sample elements contain the
high-resolution part of the time delta provided by the Jitter RNG. Usually,
this occurs in the 4 to 8 least significant bits of the sample element, but it
may vary depending on the processor.

The first step is performed by the extractlsb program, which reads the input
data, extracts the significant bits from each sample item (using a mask that
you provide) and outputs it to a bit stream file.

In the second step, the binary data streams are processed with the SP800-90B
entropy assessment tool, which calculates the min entropy.

The resulting minimum entropy for each data stream is provided in the
*.minentropy file. The log file contains a summary of the steps performed and
the output of the extractlsb program.


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

EATOOL: Path of the python program used from the Entropy Assessment tool
(usually, ea_noniid).

BUILD_EXTRACT: Indicates whether the script will build the extractlsb program.
The default is "yes".

MASK_LIST: Indicates the extraction method from each sample item. You can
indicate one or more methods; the script will generate one bit stream data
file set for each extraction method. See below for a more detailed explanation.

SAMPLES: the number of samples (time deltas) that will be extracted from the
data. The default is 1000000, as specified in SP800-90B.

### Extraction method

The kernel patch extracts raw time stamps. They are converted into time deltas
by `extractlsb.c` to obtain the time deltas uses to insert into the entropy
pool of the Jitter RNG.

Although the samples elements collected from the JitterRNG (time deltas) have
a size 64 bits, the entropy will likely be provided on the high resolution
part, which is usually the least significant bits.

Also, the python script that performs the SP800-90B entropy analysis has two
limitations:

	* although the SP800-90B standard allows alphabets of any size, the
	  script only processes alphabets up to 8 bits.

	* the script expects each sample to be contained in one byte.
  	  Therefore, if you want to use only the 4 LSB of each sample item,
	  you'll need to generate one byte per each 4-bit symbol.

You need to analyze the sample and determine which bit positions provide
the high-resolution time deltas that will feed the entropy analysis.

Usually, you can assume that the high-resolution time delta is represented
in the least significant 4 or 8 bits. So you specify the MASK_LIST parameter
as follows:

	MASK_LIST="0F:4 FF:8"

This parameter value means the following:

	* There will be two extractions methods for each data set.

	* The first method takes the 4 LSB from each sample item, generates
	  one byte per sample item, and uses a 4-bit alphabet for analyzing
	  entropy.

	* The second method takes the 8 LSB from each sample item, generates
	  one byte per item, and uses an 8-bit alphabet for analyzing entropy.

The parameter is a list of extraction methods. Each extraction method is
represented by two fields separated by a colon:

	* A mask in hexadecimal format, that indicates which bits are
	  significant. If the bit is on in a given position, this bit will be
	  considered to form the final byte. Otherwise, it'll be discarded.
	  For instance, a mask of "F8" means that the 3 LSB will be discarded,
	  and the bits 4 to 8 will be used; a mask of "7F8", means that the
	  3 LSB will be discarded, and bits 4 to 10 will be used. The bit
	  values are shifted so all bit positions in the final byte are used.

	* The second value is the alphabet size in bits. This is redundant but
	  required to avoid complex calculations in bash.

You can start with the default values, and then refine your extraction methods
if necessary. You may find that the LSB of the samples do not provide entropy,
then use a different mask to discard them.

The output of the extractlsb program can be used to detect this scenarios. The
program shows a summary of the extraction, indicating the bit positions that
have not changed in any of the samples. For example, this is the output of
the extraction program.

Processed 1000000 items from ./extractlsb samples with
mask [0x00000000000000ff] significant bits [8]

Constant 0s in sample:
00000000 00000000 00000000 00000000 --000-00 0---0--- -------- -----000

Constant 1s in sample:
-------- -------- -------- -------- -------- -------- -------- --------

You can see here that the 3 LSB of the samples always show zeroes (the minus
means that this position is variable). There you can easily determine which
positions you should consider. In this particular case, you should use a mask of
"78:4" and "7F8:8" to analyze the samples with 4-bit and 8-bit alphabets,
discarding the 3 LSB.


## Conclusion

The conclusion you have to draw is the following: To generate a 64 bit block,
the Jitter RNG obtains 64 time deltas (one time delta per bit at least, unless
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


# Example Assessment of Results

The file foldtime.O0 contains test results for the non-optimized binary code 
that is the basis for the Jitter RNG. To understand what it shows, we have to 
understand what the Jitter RNG really does: it simply measures the execution 
time of a fixed code fragment. The test does the same, i.e. it measures what 
the Jitter RNG would measure. Each time delta is simply recorded.

Each time delta is expected to contribute entropy to the entropy pool. But how 
much? We can use the SP800-90B tool set provided by NIST at [1]. This tool, 
however, can only process input data with a window size of a few bits at most. 
Thus, we take the 4 LSB of each time delta, hoping that they contain already 
sufficient entropy. 

Using the tool [1], we get the following output:

Number of Binary Symbols: 4000000

Symbol alphabet consists of 16 unique symbols

Running non-IID tests...

Running Most Common Value Estimate...
        Most Common Value Estimate (bit string) = 0.997853 / 1 bit(s)

Running Entropic Statistic Estimates (bit strings only)...
        Collision Test Estimate (bit string) = 0.933346 / 1 bit(s)
        Markov Test Estimate (bit string) = 0.999810 / 1 bit(s)
        Compression Test Estimate (bit string) = 0.749885 / 1 bit(s)

Running Tuple Estimates...
        T-Tuple Test Estimate (bit string) = 0.927240 / 1 bit(s)
        LRS Test Estimate (bit string) = 0.997939 / 1 bit(s)

Running Predictor Estimates...
        Multi Most Common in Window (MultiMCW) Prediction Test Estimate (bit string) = 0.998260 / 1 bit(s)
        Lag Prediction Test Estimate (bit string) = 0.998753 / 1 bit(s)
        Multi Markov Model with Counting (MultiMMC) Prediction Test Estimate (bit string) = 0.998283 / 1 bit(s)
        LZ78Y Prediction Test Estimate (bit string) = 0.999020 / 1 bit(s)

h': 0.749885

The last line is the key: it contains the minimum entropy in one bit of the 4 
bit snapshot

- we have 0.749885 bits of entropy per data bit

- as we analyzed 4 bits of each time delta, we get 4 * 0.749885 = 2.99954 bits
of entropy per four bit time delta

- assuming the worst case that all other bits in the time delta have no 
entropy, we have 2.99954 bits of entropy per time delta

- the Jitter RNG gathers 64 time deltas for returning 64 bits of random data 
and it uses an LFSR with a primitive and irreducible polynomial which is 
entropy preserving. Thus, the Jitter RNG collected 64 * 2.99954 = 191.97056 bits
of entropy for its 64 bit output.

- as the Jitter RNG maintains a 64 bit entropy pool, its entropy content 
cannot be larger than the pool itself. Thus, the entropy content in the pool 
after collecting 64 time deltas is max(64 bits, 191.97056 bits) = 64 bits

This implies that the Jitter RNG data has (close to) 64 bits of entropy per 
data bit.

Bottom line: When the Jitter RNG injects 64 bits of data into the Linux /dev/
random via the IOCTL, it is appropriate that the entropy estimator increases 
by 64 bits.

Bottom line: From my perspective, I see no issue in using the Jitter RNG as a 
noise source in your environments.


Note, applying the Shannon-Entropy formula to the data, we will get much 
higher entropy values.

Note II: This assessment complies with the entropy assessments to be done for 
a NIST FIP 140-2 validation compliant to FIPS 140-2 IG 7.15 

[1] https://github.com/usnistgov/SP800-90B_EntropyAssessment
