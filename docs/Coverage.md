# Coverage Report
```shell script
git clone git@github.com:awslabs/aws-lc.git
mkdir build
cd build
cmake -GNinja -DGCOV=1 ../aws-lc
ninja run_tests
lcov --directory . --capture --output-file aws-lc-combined.info
genhtml  aws-lc-combined.info
```
Open the report at build/index.html in a browser.
