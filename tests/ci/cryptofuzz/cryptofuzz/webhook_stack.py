from aws_cdk import core, \
    aws_apigateway as apigateway, \
    aws_lambda as lambda_, \
    aws_s3 as s3, \
    aws_iam as iam, \
    aws_secretsmanager as secretsmanager, \
    aws_efs as efs, \
    aws_ec2 as ec2, \
    aws_ecs as ecs, \
    aws_ecr as ecr

from util.util import EnvUtil


# Set up of infrastructure related to the GitHub Webhook and its processing.
# This includes a Lambda for SSH key generation and corpus generation, API Gateway that GitHub can send a POST
# request to when code changes, and a Lambda that will zip up the latest AWS-LC code, place it in an S3 bucket
# and run the ECS tasks. Also S3 bucket for GitHub code.
# Lastly, custom resource for triggering key generation function once during creation of resource.
class WebhookStack(core.Stack):

    def __init__(self, scope: core.Construct, id: str, **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Fetch environment variables.
        repo_owner = EnvUtil.get("GITHUB_REPO_OWNER", "13agupta")
        repo = EnvUtil.get("GITHUB_REPO", "aws-lc")
        github_code_bucket = EnvUtil.get("GITHUB_CODE_BUCKET", "github-code-bucket")
        priv_key_secret_name = EnvUtil.get("PRIVATE_KEY_SECRET_NAME", "PrivateSSHKey")
        pub_key_secret_name = EnvUtil.get("PUBLIC_KEY_SECRET_NAME", "PublicSSHKey")
        commit_secret_name = EnvUtil.get("COMMIT_SECRET_NAME", "CommitID")
        fargate_cluster_name = EnvUtil.get("FARGATE_CLUSTER_NAME", "fargate-cryptofuzz-cluster")
        report_bucket = EnvUtil.get("REPORT_BUCKET", "cryptofuzz-report-bucket")
        ubuntu_x86 = EnvUtil.get("UBUNTU_X86", "aws-lc-cryptofuzz-ubuntu-19-10--x86--clang-9x-sanitizer")
        fedora_x86 = EnvUtil.get("FEDORA_X86", "aws-lc-cryptofuzz-ubuntu-19-10--x86--clang-9x-sanitizer")
        ubuntu_aarch = EnvUtil.get("UBUNTU_AARCH", "aws-lc-cryptofuzz-ubuntu-19-10--x86--clang-9x-sanitizer")
        interesting_input_bucket = EnvUtil.get("INTERESTING_INPUT_BUCKET", "cryptofuzz-interesting-input-bucket")
        gen_corpus_container_name = EnvUtil.get("GEN_CORPUS_CONTAINER_NAME", "gen_corpus_container")
        corpus_volume = EnvUtil.get("CORPUS_VOLUME", "corpus_volume")
        security_group_name = EnvUtil.get("SECURITY_GROUP_NAME", "security-group")

        # Set up a secret to hold the private SSH key
        priv_secret = secretsmanager.Secret(self, "PrivateSSHKey",
                                            secret_name=priv_key_secret_name)

        # Set up a secret to hold the public SSH key
        pub_secret = secretsmanager.Secret(self, "PublicSSHKey",
                                           secret_name=pub_key_secret_name)

        # Set up a secret to store the commit ID
        self.commit_secret = secretsmanager.Secret(self, "CommitID",
                                                   secret_name=commit_secret_name)

        # Set up GitHub Code Bucket
        code_bucket = s3.Bucket(self, "GitHub Code Bucket",
                                bucket_name=github_code_bucket)  # Maybe something that should be changed in the future,
        # as it will cause errors if the bucket name has been taken already

        # Creating VPC with Internet Gateway
        self.vpc = ec2.Vpc(self, "vpc",
                           max_azs=2,
                           nat_gateways=1)

        # Selecting subnets
        selection = self.vpc.select_subnets()
        subnets = [subnet.subnet_id for subnet in selection.subnets]

        # Creating a security group
        security_group = ec2.SecurityGroup(self, "Security Group",
                                           security_group_name=security_group_name,
                                           vpc=self.vpc)

        # Creating EFS filesystem to store corpus
        file_system = efs.FileSystem(self, "Corpus File System",
                                     vpc=self.vpc,
                                     encrypted=True,
                                     security_group=security_group)

        # Upload docker image for corpus generation into an ECR repo to be used in the below lambda function
        corpus_gen_ecr_repo = ecr.Repository(self, gen_corpus_container_name,
                                             image_scan_on_push=True,
                                             repository_name=gen_corpus_container_name)

        corpus_gen_ecr_image = ecs.EcrImage(corpus_gen_ecr_repo, 'latest')

        corpus_gen_ecr_image.from_asset("../docker_files/linux-x86/cryptofuzz_generate_corpus")

        # So that lambda functions can run ECS tasks with the appropriate permissions
        ecs_run_task_policy = iam.PolicyDocument.from_json(
            {
                "Version": "2012-10-17",
                "Statement": [
                    {
                        "Sid": "Stmt1512361420000",
                        "Effect": "Allow",
                        "Action": [
                            "ecs:RunTask"
                        ],
                        "Resource": [
                            "*"
                        ]
                    },
                    {
                        "Sid": "Stmt1512361593000",
                        "Effect": "Allow",
                        "Action": [
                            "iam:PassRole"
                        ],
                        "Resource": [
                            "*"
                        ]
                    }
                ]
            }
        )

        # So that lambda functions can log to CloudWatch
        cloudwatch_log_policy = iam.PolicyDocument.from_json(
            {
                "Version": "2012-10-17",
                "Statement": [
                    {
                        "Effect": "Allow",
                        "Action": [
                            "logs:CreateLogGroup",
                            "logs:CreateLogStream",
                            "logs:PutLogEvents",
                            "logs:DescribeLogStreams"
                        ],
                        "Resource": [
                            "arn:aws:logs:*:*:*"
                        ]
                    }
                ]
            }
        )

        inline_policies = {"ecs_run_task_policy": ecs_run_task_policy, "cloudwatch_log_policy": cloudwatch_log_policy}
        ssh_handler_role = iam.Role(self, "SSH Handler Role",
                                    assumed_by=iam.ServicePrincipal("lambda.amazonaws.com"),
                                    inline_policies=inline_policies,
                                    managed_policies=[
                                        iam.ManagedPolicy.from_aws_managed_policy_name("AmazonECS_FullAccess")
                                    ])

        # Set up Lambda function for handling SSH key generation
        ssh_handler = lambda_.Function(self, "SSH Handler",
                                       runtime=lambda_.Runtime.PYTHON_3_7,
                                       code=lambda_.Code.from_asset("CreateSSHKey"),
                                       handler="lambda_function.lambda_handler",
                                       environment={
                                           "PRIVATE_KEY_SECRET_NAME": priv_key_secret_name,
                                           "PUBLIC_KEY_SECRET_NAME": pub_key_secret_name,
                                           "GEN_CORPUS_CONTAINER_NAME": gen_corpus_container_name,
                                           "GEN_CORPUS_IMAGE": corpus_gen_ecr_repo.repository_uri,
                                           "CORPUS_VOLUME": corpus_volume,
                                           "CORPUS_FILE_SYSTEM_ID": file_system.file_system_id,
                                           "SUBNET_ID": subnets[0],
                                           "FARGATE_CLUSTER_NAME": fargate_cluster_name,
                                           "SECURITY_GROUP_NAME": security_group_name
                                       },
                                       role=ssh_handler_role,
                                       timeout=core.Duration.minutes(5))

        # Allow writing to secret in Secrets Manager
        priv_secret.grant_write(ssh_handler)
        pub_secret.grant_write(ssh_handler)

        # Set up custom resource to call lambda function once during creation (other lifecycle events are ignored
        # by the lambda function) of the stack
        cr = core.CustomResource(self, "Generate SSH Key Resource",
                                 service_token=ssh_handler.function_arn)

        ssh_handler_ref = core.Reference(value="SSH Handler Ref",
                                         target=ssh_handler)

        # Make SSH Public Key secret name a part of the output of the Cloud Formation stack
        public_key = core.CfnOutput(self, "Pulic Key Secret Name",
                                    value=pub_key_secret_name)

        git_handler_role = iam.Role(self, "Git Handler Role",
                                    assumed_by=iam.ServicePrincipal("lambda.amazonaws.com"),
                                    inline_policies=inline_policies,
                                    managed_policies=[
                                        iam.ManagedPolicy.from_aws_managed_policy_name("AmazonECS_FullAccess"),
                                        iam.ManagedPolicy.from_aws_managed_policy_name("AmazonS3FullAccess")
                                    ])

        # Set up Lambda function for handling zipping up code and running ECS tasks
        git_handler = lambda_.Function(self, "Webhook Handler",
                                       runtime=lambda_.Runtime.PYTHON_3_7,
                                       code=lambda_.Code.from_asset("GitPullS3"),
                                       handler="lambda_function.lambda_handler",
                                       environment={
                                           "GITHUB_CODE_BUCKET": github_code_bucket,
                                           "PRIVATE_KEY_SECRET_NAME": priv_key_secret_name,
                                           "PUBLIC_KEY_SECRET_NAME": pub_key_secret_name,
                                           "FARGATE_CLUSTER_NAME": fargate_cluster_name,
                                           "INTERESTING_INPUT_BUCKET": interesting_input_bucket,
                                           "REPORT_BUCKET": report_bucket,
                                           "UBUNTU_X86": ubuntu_x86,
                                           "FEDORA_X86": fedora_x86,
                                           "UBUNTU_AARCH": ubuntu_aarch,
                                           "GITHUB_REPO_OWNER": repo_owner,
                                           "GITHUB_REPO": repo,
                                           "COMMIT_SECRET_NAME": commit_secret_name,
                                           "SUBNET_ID": subnets[0]
                                       },
                                       timeout=core.Duration.minutes(5),
                                       role=git_handler_role)

        # Allow reading secret from Secrets Manager and read/write from necessary S3 buckets
        priv_secret.grant_read(git_handler)
        pub_secret.grant_read(git_handler)
        self.commit_secret.grant_write(git_handler)
        code_bucket.grant_read_write(git_handler)

        # Set up API Gateway
        api = apigateway.RestApi(self, "webhook-api",
                                 rest_api_name="Webhook Service",
                                 description="This service connects to a GitHub Webhook")

        # Attach Lambda Function to API Gateway
        get_webhook_integration = \
            apigateway.LambdaIntegration(git_handler)

        # Allow HTTP POST requests
        api.root.add_method("POST", get_webhook_integration,
                            method_responses=[
                                apigateway.MethodResponse(status_code="200")
                            ])
