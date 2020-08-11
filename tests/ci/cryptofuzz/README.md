## Overview

AWS-LC Fuzzing CI uses AWS CDK to define and deploy AWS resources (e.g. AWS Lambda, ECR).

## CI Setup

### Before running CDK command:

* Install [AWS CDK](https://docs.aws.amazon.com/cdk/latest/guide/getting_started.html#getting_started_install)
* Install [AWS CLI](https://docs.aws.amazon.com/cli/latest/userguide/install-cliv2.html)
* [Connect GitHub and AWS account using access token](https://docs.aws.amazon.com/codebuild/latest/userguide/sample-access-tokens.html)
* Install python 3.7 and associated pip

### Minimal permissions:

To setup or update the CI in your account you will need the following IAM permissions. 

* CloudWatch
  * logs:CreateLogGroup
  * logs:CreateLogStream
  * logs:DescribeLogGroups
  * logs:DescribeLogStreams
  * logs:PutLogEvents
  * logs:GetLogEvents
  * logs:FilterLogEvents
* ECS
  * ecr:GetAuthorizationToken
  * ecr:BatchCheckLayerAvailability
  * ecr:GetDownloadUrlForLayer
  * ecr:BatchGetImage
* ECR
  * ecr:Batch*
  * ecr:Get*
  * ecr:Describe*
  * ecr:List*
  * ecr:Initiate*
  * ecr:Upload*
  * ecr:Complete*
  * ecr:Put*
* IAM
  * iam:PassRole
* S3
  * s3:*
* SecretsManager
  * secretsmanager:GetSecretValue
  * secretsmanager:DescribeSecret
  * secretsmanager:PutSecretValue
  * secretsmanager:UpdateSecret

### Command
Before running the command with the action that you would like to perform, set the following environment variables appropriately:
```
export CDK_DEPLOY_ACCOUNT={aws-account-id}
export CDK_DEPLOY_REGION={region}
export GITHUB_REPO_OWNER={github-repo-owner}
```

Afterwards, clone the aws-lc-cryptofuzz repository and place it in this directory (aws-lc/tests/ci/cryptofuzz):
```
git clone https://git-codecommit.us-east-2.amazonaws.com/v1/repos/aws-lc-cryptofuzz
```

To make sure all docker files have the appropriate build context before they are uploaded to Amazon ECR, run the following in the docker_images directory (aws-lc/tests/ci/docker_images):
```
./configure_build_contexts.sh
```

Lastly, you will have to install dependencies for each of the lambda functions, to complete their build packages before they are uploaded to AWS Lambda. You can do so using the following script:
```
./install_lambda_deps.sh
```

Then, you can proceed with the general commands.
General command:
```
$ ./run-cryptofuzz.sh {ACTION}
```

#### Examples

To see the synthesized CloudFormation template, run command:
```
./run-cryptofuzz.sh SYNTH
```

To set up AWS-LC Fuzzing CI, run command:
```
./run-cryptofuzz.sh DEPLOY
```
Afterwards, you will get two stack outputs. One of them is the API Gateway Endpoint link, while the other is the name of the Secret in SecretsManager that holds the SSH public key. To finish setting up the CI, add the public key to your GitHub account, and setup a GitHub Webhook using the API Gateway Endpoint link.

Make sure that there is a task with task definition called "gen_corpus_container" running in the ECS cluster "fargate-cryptofuzz-cluster". If you see that it didn't start running (for example, if there was a connection failure of any sort), then you will have to manually run the task. In the ECS console, go to Clusters (in the left bar) -> fargate-cryptofuzz-cluster -> Tasks -> Run New Task. Run the task with the following configurations:

* Launch type: Fargate
* Task Definition: gen_corpus_container
* Platform Version: 1.4.0 (Not the default of LATEST)
* Cluster VPC (you will need to select the VPC created by the CloudFormation WebhookStack)
  * Go to CloudFormation -> Stacks -> WebhookStack -> Resources, and you should see the ID of the VPC that was created by CloudFormation
* Subnets: Choose all of them
* Security Groups: Click Edit -> Select existing Security Group, and check security-group
* Auto-assign public IP: ENABLED

To destroy all AWS resources created above, run command:
```
# This command does not delete S3, ECR, and EFS, which require manual deletion.
./run-cryptofuzz.sh DESTROY
```

To compare deployed stack with current state, run command:
```
./run-cryptofuzz.sh DIFF
```

## Files

Inspired by [AWS CDK blog](https://aws.amazon.com/blogs/developer/getting-started-with-the-aws-cloud-development-kit-and-python/)

Below is CI file structure.

```
(.env) $ tree
.
├── CreateSSHKey
│   ├── lambda_function.py
├── GitPullS3
│   ├── lambda_function.py
├── ReportFunction
│   ├── lambda_function.py
├── README.md
├── app.py
├── cdk
│   ├── __init__.py
│   ├── webhook_stack.py
│   ├── fuzzing_stack.py
│   ├── report_stack.py
├── cdk.json
├── requirements.txt
├── run-cryptofuzz.sh
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
