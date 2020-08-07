#!/bin/bash

# Wrapper to run cryptofuzz so that docker image doesn't exit when a failure is detected by cryptofuzz
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
