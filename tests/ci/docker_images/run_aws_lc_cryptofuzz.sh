#!/bin/bash

set -e
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
cd / 
chmod +x cryptofuzz.sh 
./cryptofuzz.sh 
