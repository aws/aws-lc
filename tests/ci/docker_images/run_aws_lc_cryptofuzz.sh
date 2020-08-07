# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
#!/bin/bash

set -exuo pipefail

# -e: Exit on any failure
# -x: Print the command before running
# -u: Any variable that is not set will cause an error if used
# -o pipefail: Makes sure to exit a pipeline with a non-zero error code if any command in the pipeline exists with a
#              non-zero error code.

# Set necessary environment variables
chmod +x /env.sh
source /env.sh

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

