## Overview

AWS-LC CI uses AWS CDK to define and deploy AWS resources (e.g. AWS CodeBuild, ECR).

## CI Setup

### Before running CDK command:

* Install [AWS CDK](https://docs.aws.amazon.com/cdk/latest/guide/getting_started.html#getting_started_install)
* Install [AWS CLI](https://docs.aws.amazon.com/cli/latest/userguide/install-cliv2.html)
* [Connect GitHub and AWS account using access token](https://docs.aws.amazon.com/codebuild/latest/userguide/sample-access-tokens.html)

### Minimal permissions:

To setup or update the CI in your account you will need the following IAM permissions. 

* CodeBuild
  * codebuild:Create*
  * codebuild:Update*
  * codebuild:Batch*
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

### Command

```
$ ./run-cdk.sh {aws-account-id} {region} {github-repo-owner} {github-repo-name} {ACTION}
```

#### Examples

To see the synthesized CloudFormation template, run command:
```
./run-cdk.sh 123456789 us-west-2 GitHubUserName aws-lc SYNTH
```

To set up AWS-LC CI in AWS account `123456789` for the forked GitHub repository `https://github.com/GitHubUserName/aws-lc`, run command:
```
./run-cdk.sh 123456789 us-west-2 GitHubUserName aws-lc DEPLOY
```

To destroy all AWS resources created above, run command:
```
# This command does not delete S3 and ECR, which require manually deletion.
./run-cdk.sh 123456789 us-west-2 GitHubUserName aws-lc DESTROY
```

To compare deployed stack with current state, run command:
```
./run-cdk.sh 123456789 us-west-2 GitHubUserName aws-lc DIFF
```

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
│   ├── github_codebuild_stack.py
│   ├── linux_docker_images_build_stack.py
│   ├── windows_docker_build_ssm_document.yaml
│   └── windows_docker_image_build_stack.py
├── cdk.json
├── requirements.txt
├── run-cdk.sh
├── setup.py
└── util
    ├── __init__.py
    └── util.py
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
