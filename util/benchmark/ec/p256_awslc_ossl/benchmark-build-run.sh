
BENCH_DIR=$PWD
AWSLC_DIR=$BENCH_DIR/../aws-lc
OPENSSL_DIR=$BENCH_DIR/../openssl
PROJECT=benchmark_ec_p256

# Process input parameters and append them to the options string
options=''
while [[ "$#" -gt 0 ]]; do
    case $1 in
        -t|--test)
            options+=" -t $2";
            shift ;;
        -i|--iterations)
            options+=" -i $2";
            shift ;;
        *)
            echo "Unknown parameter passed: $1"; exit 1 ;;
    esac
    shift
done

echo "Options: $options"

# Check that AWS-LC directory exists
if [[ ! -d $AWSLC_DIR ]]
then
    echo "$AWS-LC directory not found"; exit 1;
## checkout AWS-LC if it doesn't exist already
#     echo "Checkout AWS-LC main tip" && \
#         cd .. && \
#         git clone https://github.com/awslabs/aws-lc.git && \
#         cd $BENCH_DIR
fi

# build AWS-LC
echo "Build AWS-LC" && \
    cd $AWSLC_DIR && \
    mkdir -p build && \
    cd build && \
    cmake -DOPENSSL_AARCH64_P256=1 -DCMAKE_BUILD_TYPE=Release -GNinja .. && \
    ninja && \
    cd $BENCH_DIR

# checkout OpenSSL if it doesn't exist already
if [[ ! -d $OPENSSL_DIR ]]
then
    echo "Checkout tag OpenSSL_1_1_1h from OpenSSL" && \
        cd .. && \
        git clone --branch OpenSSL_1_1_1h --single-branch https://github.com/openssl/openssl.git && \
        cd $BENCH_DIR
fi

# build OpenSSL if libcrypto.a doesn't exist
[[ ! -f $OPENSSL_DIR/libcrypto.a ]] && \
    echo "Build OpenSSL" && \
    cd $OPENSSL_DIR && \
    ./config && \
    make && \
    cd $BENCH_DIR

# build benchmark binaries
echo "Build benchmark binaries" && \
    mkdir -p build && \
    cd build && \
    cmake .. && \
    cmake --build .
# run benchmarks
echo
echo "Run P-256 AWS-LC benchmarks"
./${PROJECT}_awslc $options

echo
echo "Run P-256 OPENSSL benchmarks"
if [[ "$OSTYPE" == "darwin"* ]]
then
    DYLD_LIBRARY_PATH=${OPENSSL_DIR} ./${PROJECT}_ossl $options
else
    LD_LIBRARY_PATH=${OPENSSL_DIR} ./${PROJECT}_ossl $options
fi
