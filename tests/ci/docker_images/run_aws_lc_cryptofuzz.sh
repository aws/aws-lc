#!/bin/bash

set -e
# Build aws-lc and corresponding module in aws-lc-cryptofuzz
aws s3 cp s3://${GITHUB_CODE_BUCKET}/${REPO_OWNER}/${REPO_NAME}/${REPO_OWNER}_${REPO_NAME}.zip ./ 
unzip ${REPO_OWNER}_${REPO_NAME}.zip -d aws-lc 
cd / 
ls 
cd aws-lc/ 
mkdir build/ 
cd build/ 
cmake -DCMAKE_CXX_FLAGS="$CXXFLAGS" -DCMAKE_C_FLAGS="$CFLAGS" -DBORINGSSL_ALLOW_CXX_RUNTIME=1 .. 
make crypto -j$(nproc) 
cd / 
cd aws-lc-cryptofuzz/modules/openssl/ 
make 

# Run aws-lc-cryptofuzz and write interesting inputs to corpus/S3 bucket
cd /
cd aws-lc-cryptofuzz/
make
./cryptofuzz /mount/efs/corpus/ -max_total_time=100
mkdir ../${BUILD_CONFIGURATION}/
cp crash* ../${BUILD_CONFIGURATION}/
cp crash* /mount/efs/corpus/
cp leak* ../${BUILD_CONFIGURATION}/
cp crash* /mount/efs/corpus/
cp timeout* ../${BUILD_CONFIGURATION}/
cp timeout* /mount/efs/corpus/
cd ../
aws s3 mv ${BUILD_CONFIGURATION} s3://${INTERESTING_INPUT_BUCKET}/${COMMIT_ID}/${BUILD_CONFIGURATION}/ --recursive
ls

