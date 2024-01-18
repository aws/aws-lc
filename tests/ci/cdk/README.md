## Overview

AWS-LC CI uses AWS CDK to define and deploy AWS resources (e.g. AWS CodeBuild, ECR).

## CI Setup

### Before running CDK command:

* Install [AWS CDK](https://docs.aws.amazon.com/cdk/latest/guide/getting_started.html#getting_started_install)
* Install [AWS CLI](https://docs.aws.amazon.com/cli/latest/userguide/install-cliv2.html)
* [Connect AWS CodeBuild with GitHub](https://docs.aws.amazon.com/codebuild/latest/userguide/sample-access-tokens.html)
  * Note: This step should grant AWS CodeBuild with access to create WebHook.
  * For team AWS account, AWS CodeBuild is connected with GitHub through GitHub OAuth.
    * step 1: go to AWS CodeBuild console.
    * step 2: create a CodeBuild project.
    * step 3: change **Source provider** to **GitHub**. 
    * step 4: click **Connect using OAuth** and **Connect to GitHub**.
    * step 5: follow the OAuth app to grant access.
* Setup Python environment:
  * From `aws-lc/tests/ci` run:
```shell
python -m pip install -r requirements.txt
```

### Minimal permissions:

To setup or update the CI in your account you will need the following IAM permissions. 

* CodeBuild
  * codebuild:Create*
  * codebuild:Update*
  * codebuild:Batch*
  * codebuild:StartBuild
  * codebuild:StopBuild
  * codebuild:RetryBuild
* EC2
  * ec2:Describe*
  * ec2:Create*
  * ec2:RunInstances
  * ec2:TerminateInstances
* ECR
  * ecr:Batch*
  * ecr:Get*
  * ecr:Describe*
  * ecr:List*
  * ecr:Initiate*
  * ecr:Upload*
  * ecr:Complete*
  * ecr:Put*
* S3
  * s3:Put*
  * s3:Get*
* SSM
  * ssm:Describe*
  * ssm:List*
  * ssm:Get*
  * ssm:Put*
  * ssm:Update*
  * ssm:List*
* SecretsManager
  * secretsmanager:CreateSecret
  * secretsmanager:PutSecretValue
  * secretsmanager:DeleteSecret
  * secretsmanager:GetSecretValue

### Commands

These commands are run from `aws-lc/tests/ci/cdk`. \
If not done previously, bootstrap cdk before running the commands below:
```shell
cdk bootstrap aws://${AWS_ACCOUNT_ID}/us-west-2
```

You may also need to request an increase to certain account quotas:
```shell
open https://${CDK_DEPLOY_REGION}.console.aws.amazon.com/servicequotas/home/services/ec2/quotas
```
* **EC2-VPC Elastic IPs** = 20

Note: `GITHUB_REPO_OWNER` specifies the GitHub repo targeted by this CI setup.
* https://github.com/${GITHUB_REPO_OWNER}/aws-lc.git

To set up AWS-LC CI, run command:
```
./run-cdk.sh --github-repo-owner ${GITHUB_REPO_OWNER} --action deploy-ci --aws-account ${AWS_ACCOUNT_ID}
```

To update AWS-LC CI, run command:
```
./run-cdk.sh --github-repo-owner ${GITHUB_REPO_OWNER} --action update-ci --aws-account ${AWS_ACCOUNT_ID}
```

To create/update Linux Docker images, run command:
```
./run-cdk.sh --github-repo-owner ${GITHUB_REPO_OWNER} --action build-linux-img --aws-account ${AWS_ACCOUNT_ID}
```

To destroy AWS-LC CI resources created above, run command:
```
# NOTE: this command will destroy all resources (AWS CodeBuild and ECR).
./run-cdk.sh --github-repo-owner ${GITHUB_REPO_OWNER} --action destroy-ci --aws-account ${AWS_ACCOUNT_ID}
```

For help, run command:
```
./run-cdk.sh --help
```

## AWS-LC Benchmarking Framework

### Framework Setup
No special actions outside those outlined in the **CI Setup** section are required to deploy the benchmarking framework to an AWS account and GitHub repository.

Specific implementation details can mostly be found in:
* `run-cdk.sh`
* `cdk/bm_framework_stack.py`

### How to Use
After the benchmarking framework is set up, there are multiple ways to start the process.

Note: due to the nature of how the framework works, a commit containing the relevant scripts (located inside `tests/ci/benchmark_framework/`,`tests/ci/build_run_benchmarks.sh`, and `tests/ci/run_bm_framework.sh`) is required for a successful run of the framework. If these files are not present, the benchmarking process will fail.

#### Start from Pull Request
Opening, reopening, or updating a pull request in a repository in which the framework has been deployed to will start the benchmarking process automatically without any extra input needed from the user.

#### Start Locally
Starting the benchmarking framework locally still requires the user's AWS CLI to be configured for an account with the framework deployed to it. Additionally, several environment variables need to be set for the framework to work correctly.

| Environment Variable      | Description            | Value                                                                         |
|---------------------------|------------------------|-------------------------------------------------------------------------------|
| `CODEBUILD_SOURCE_VERSION`  | GitHub Commit ID       | The commit ID of the version of AWS-LC to be benchmarked                      |
| `CODEBUILD_SOURCE_REPO_URL` | GitHub Repository Link | The link used to clone the repository which the provided commit ID belongs to |

After setting the environment variables, run `./tests/ci/run_bm_framework` from the root directory of the project to start the benchmarking process. This is the same script that is run by a CodeBuild instance that is used when the framework is started via a PR.

#### Examine Output
After it is started, the benchmarking framework will take 30-45 minutes to complete. Once finished, the benchmarking script will exit with an error if a regression was detected. If the framework was started from a PR, this will result in a failed CI vote.

If necessary, logs of both the CodeBuild (if started via a pull request) and SSM Run Commands can be found in AWS CloudWatch Logs in order to help determine causes of failure. Performance and regression information can be found in S3 buckets called `<AWS ACCOUNT ID>-aws-lc-ci-bm-framework-prod-bucket` and `<AWS_ACCOUNT_ID>-aws-lc-ci-bm-framework-pr-bucket`. The former holds the performance results of the tip of main of AWS-LC and FIPS compliant AWS-LC, BoringSSL, and OpenSSL, while the latter holds performance information and results for the PR versions of AWS-LC and FIPS compliant AWS-LC. These results are in a folder labeled by the GitHub commit ID of the version of AWS-LC that is being tested.

Each file output by the CI will have a prefix with some processor information in it, following the format `<processor architecture><hardware support type>-`. So for example a file labeled `amd64noavx-aws-lc-pr_bm.csv` would contain benchmarking information for the PR version of AWS-LC being run on an x86 processor without AVX support, while a file labeled `amd64-prod_vs_pr.csv` would contain a performance comparison between the tip of main of AWS-LC and the PR version of AWS-LC on an x86 processor with all hardware support enabled.

## Files

Inspired by [AWS CDK blog](https://aws.amazon.com/blogs/developer/getting-started-with-the-aws-cloud-development-kit-and-python/)

Below is CI file structure.

```
(.env) $ tree
.
├── README.md
├── app.py
├── cdk
│   ├── __init__.py
│   ├── ecr_stack.py
│   ├── ...
├── cdk.json
├── requirements.txt
├── run-cdk.sh
├── setup.py
└── util
    ├── __init__.py
    └── env_util.py
    └── ...
```
* `README.md` — The introductory README for this project.
* `app.py` — The “main” for this sample application.
* `cdk.json` — A configuration file for CDK that defines what executable CDK should run to generate the CDK construct tree.
* `cdk` — A CDK module directory
* `requirements.txt` — This file is used by pip to install all of the dependencies for your application. In this case, it contains only -e . This tells pip to install the requirements specified in setup.py. It also tells pip to run python setup.py develop to install the code in the cdk module so that it can be edited in place.
* `setup.py` — Defines how this Python package would be constructed and what the dependencies are.

## Development Reference

The `cdk.json` file tells the CDK Toolkit how to execute this CDK app `app.py`.

This project is set up like a standard Python project.  The initialization
process also creates a virtualenv within this project, stored under the .env
directory.  To create the virtualenv it assumes that there is a `python3`
(or `python` for Windows) executable in your path with access to the `venv`
package. If for any reason the automatic creation of the virtualenv fails,
you can create the virtualenv manually.

To manually create a virtualenv on MacOS and Linux:

```
$ python3 -m venv .env
```

After the init process completes and the virtualenv is created, you can use the following
step to activate your virtualenv.

```
$ source .env/bin/activate
```

If you are a Windows platform, you would activate the virtualenv like this:

```
% .env\Scripts\activate.bat
```

Once the virtualenv is activated, you can install the required dependencies.

```
$ pip install -r requirements.txt
```

At this point you can now synthesize the CloudFormation template for this code.

```
$ cdk synth
```

To add additional dependencies, for example other CDK libraries, just add
them to your `setup.py` file and rerun the `pip install -r requirements.txt`
command.

### Useful commands

 * `cdk ls`          list all stacks in the app
 * `cdk synth`       emits the synthesized CloudFormation template
 * `cdk deploy`      deploy this stack to your default AWS account/region
 * `cdk diff`        compare deployed stack with current state
 * `cdk docs`        open CDK documentation
 
### Useful Docker image build commands

**Notes**:
* below commands replicate steps that are performed in `run-cdk.sh` but use default values set in `cdk/util/metadata.py`.
* Always clean up resources set up for Docker image build.
  * `cdk destroy aws-lc-docker-image-build-* --force`

#### Linux Docker image build

```bash
# Launch Linux Docker image CodeBuild resources.
cdk deploy aws-lc-docker-image-build-linux --require-approval never

# Trigger CodeBuild to build Linux Docker Images
aws codebuild start-build-batch --project-name aws-lc-docker-image-build-linux

# Go to AWS console, you can check CodeBuild by clicking "Developer Tools > CodeBuild > Build projects".
```

#### Windows Docker image build
Windows docker image build requires more resources (like EC2 host, S3, SSM and so on) set up because DIND (Docker in Docker) is not supported by Windows.
Below are some commands specific to windows docker image build.
 
```bash
# Define environment variables needed by Windows docker image build.
DATE_NOW="$(date +%Y-%m-%d-%H-%M)"
export AWS_LC_S3_BUCKET_PREFIX='aws-lc-windows-docker-image-build-s3'
export S3_FOR_WIN_DOCKER_IMG_BUILD="${AWS_LC_S3_BUCKET_PREFIX}-${DATE_NOW}"
export WIN_EC2_TAG_KEY='aws-lc'
export WIN_EC2_TAG_VALUE="aws-lc-windows-docker-image-build-${DATE_NOW}"
export WIN_DOCKER_BUILD_SSM_DOCUMENT="windows-ssm-document"

# Clean up all Windows docker image build resources.
cdk destroy aws-lc-docker-image-build-windows --force
aws s3 rm "s3://${S3_FOR_WIN_DOCKER_IMG_BUILD}" --recursive
aws s3api delete-bucket --bucket "${S3_FOR_WIN_DOCKER_IMG_BUILD}"

# Deploy Windows docker image build resources.
cdk deploy aws-lc-docker-image-build-windows --require-approval never

# Sleep 10 minutes so Windows EC2 is ready to execute SSM commands.
sleep 600

# Trigger SSM commands to build Windows Docker Images.
instance_id=$(aws ec2 describe-instances \
    --filters "Name=tag:${WIN_EC2_TAG_KEY},Values=${WIN_EC2_TAG_VALUE}" | jq -r '.Reservations[0].Instances[0].InstanceId')
aws ssm send-command \
        --instance-ids "${instance_id}" \
        --document-name "${WIN_DOCKER_BUILD_SSM_DOCUMENT}" \
        --output-s3-bucket-name "${S3_FOR_WIN_DOCKER_IMG_BUILD}" \
        --output-s3-key-prefix 'ssm-runcommand-logs'

# Go to AWS console, you can check run command by clicking `AWS Systems Manager > Run Command`.
```
