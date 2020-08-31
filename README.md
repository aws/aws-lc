# AWS Lib Crypto (aws-lc) Public Preview

AWS Lib Crypto (aws-lc) is a cryptographic library originally forked from BoringSSL and is designed to cater to AWS's needs.  This library will be supported and ehnanced by crypto experts within Amazon.  

## Quickstart for Ubuntu
1. Setup required dependencies
```
sudo apt update
sudo apt install build-essentials
sudo apt install ninja-build
sudo apt install quilt
sudo wget https://dl.google.com/go/go1.13.12.linux-amd64.tar.gz
tar -xvf go1.13.12.linux-amd64.tar.gz
mv go /usr/local
export GOROOT=/usr/local/go
export PATH="$GOROOT/bin:$PATH"
```
2. Fork aws-lc on Github
```
git clone https://github.com/${YOUR_GITHUB_ACCOUNT_NAME}/aws-lc.git
mkdir awslc-install awslc-build
```
3. Execute build and tests
```
cd awslc-build
cmake -GNinja -DCMAKE_INSTALL_PREFIX=$(pwd)/../awslc-install ..
ninja install

//Execute tests when required
ninja run_tests

```

## Have a Question?
If you have any questions about Submitting PR's, Opening Issues, aws-lc API usage, or any similar topic, we have a public chatroom available here to answer your questions: https://gitter.im/awslabs/aws-lc

Otherwise, if you think you might have found a security impacting issue, please instead follow [our Security Notification Process.](#security-issue-notifications)

## Security issue notifications
If you discover a potential security issue in s2n we ask that you notify
AWS Security via our [vulnerability reporting page](http://aws.amazon.com/security/vulnerability-reporting/). Please do **not** create a public github issue. 
