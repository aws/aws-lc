from aws_cdk import core, \
    aws_apigateway as apigateway, \
    aws_lambda as lambda_, \
    aws_s3 as s3, \
    aws_iam as iam, \
    aws_secretsmanager as secretsmanager, \
    aws_efs as efs, \
    aws_ec2 as ec2, \
    aws_ecr_assets as ecr_assets


# Set up of infrastructure related to the GitHub Webhook and its processing.
# Here is the list of infrastructure that is included in this stack:
# Public and private key secrets in Secrets Manager
# S3 bucket to store the latest, code in aws-lc (zipped)
# VPC with a single NAT gateway
# Security group that allows all inbound and outbound traffic
# ECR repositories for each of the docker files relating to cryptofuzz
# Lambda function for generating SSH key, generating corpus, and creating task definitions for build configurations
# Lambda function that handles requests coming from GitHub (zips latest code and runs cryptofuzz on build configurations)
# (Also associated IAM policies/roles)
# API gateway with lambda integration
class WebhookStack(core.Stack):

    def __init__(self, scope: core.Construct, id: str, env, **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Set up a secret to hold the private SSH key
        priv_secret = secretsmanager.Secret(self, "PrivateSSHKey",
                                            secret_name=env['priv_key_secret_name'])

        # Set up a secret to hold the public SSH key
        pub_secret = secretsmanager.Secret(self, "PublicSSHKey",
                                           secret_name=env['pub_key_secret_name'])

        # Set up a secret to store the commit ID
        self.commit_secret = secretsmanager.Secret(self, "CommitID",
                                                   secret_name=env['commit_secret_name'])

        # Set up GitHub Code Bucket
        code_bucket = s3.Bucket(self, "GitHub Code Bucket",
                                bucket_name=env['github_code_bucket'])

        # Creating VPC with Internet Gateway
        self.vpc = ec2.Vpc(self, "vpc",
                           max_azs=2,
                           nat_gateways=1)

        # Selecting subnets
        selection = self.vpc.select_subnets()
        subnets = [subnet.subnet_id for subnet in selection.subnets]

        security_group = ec2.SecurityGroup(self, "corpus security group",
                                           vpc=self.vpc,
                                           security_group_name=env['security_group_name'])

        security_group.add_ingress_rule(ec2.Peer.any_ipv4(), ec2.Port.all_traffic())

        # Creating EFS filesystem to store corpus
        file_system = efs.FileSystem(self, "Corpus File System",
                                     vpc=self.vpc,
                                     security_group=security_group,
                                     encrypted=True)

        # Upload all docker images into their own repositories
        corpus_gen_ecr_image = ecr_assets.DockerImageAsset(self, "gen_corpus_image",
                                                           repository_name=env['gen_corpus_container_name'],
                                                           directory='../docker_images/linux-x86/cryptofuzz_generate_corpus')

        ubuntu_x86_image = ecr_assets.DockerImageAsset(self, "ubuntu_x86",
                                                       repository_name="ubuntu_x86",
                                                       directory='../docker_images/linux-x86/cryptofuzz_ubuntu-19.10_clang-9x_sanitizer')

        fedora_x86_image = ecr_assets.DockerImageAsset(self, "fedora_x86",
                                                       repository_name="ubuntu_aarch",
                                                       directory='../docker_images/linux-x86/cryptofuzz_fedora-31_clang-9x')

        ubuntu_aarch_image = ecr_assets.DockerImageAsset(self, "ubuntu_aarch",
                                                         repository_name="ubuntu_aarch",
                                                         directory='../docker_images/linux-aarch/cryptofuzz_ubuntu-19.10_clang-9x_sanitizer')

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

        # So that ECS tasks can create their own CloudWatch logs
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

        # So that ECS tasks can pull from the appropriate ECS repo
        ecs_task_execution_role_policy = iam.PolicyDocument.from_json(
            {
                "Version": "2012-10-17",
                "Statement": [
                    {
                        "Effect": "Allow",
                        "Action": [
                            "ecr:GetAuthorizationToken",
                            "ecr:BatchCheckLayerAvailability",
                            "ecr:GetDownloadUrlForLayer",
                            "ecr:BatchGetImage",
                            "logs:CreateLogStream",
                            "logs:PutLogEvents"
                        ],
                        "Resource": "*"
                    }
                ]
            }
        )

        # Creating task role for ECS containers
        inline_policies = {"cloudwatch_log_policy": cloudwatch_log_policy}

        task_role = iam.Role(self, "S3 Full Access Role",
                             assumed_by=iam.ServicePrincipal("ecs-tasks.amazonaws.com"),
                             inline_policies=inline_policies,
                             managed_policies=[
                                 iam.ManagedPolicy.from_aws_managed_policy_name("AmazonS3FullAccess")
                             ])

        # Creating execution role for ECS containers
        inline_policies.update({'ecs_task_execution_role_policy': ecs_task_execution_role_policy})

        execution_role = iam.Role(self, "ECS Task Execution Role",
                                  assumed_by=iam.ServicePrincipal("ecs-tasks.amazonaws.com"),
                                  inline_policies=inline_policies)

        # Set up Lambda function for handling SSH key generation
        ssh_handler = lambda_.Function(self, "SSH Handler",
                                       runtime=lambda_.Runtime.PYTHON_2_7,
                                       code=lambda_.Code.from_asset("CreateSSHKey"),
                                       handler="lambda_function.lambda_handler",
                                       environment={
                                           "PRIVATE_KEY_SECRET_NAME": env['priv_key_secret_name'],
                                           "PUBLIC_KEY_SECRET_NAME": env['pub_key_secret_name'],
                                           "GEN_CORPUS_CONTAINER_NAME": env['gen_corpus_container_name'],
                                           "UBUNTU_X86_CONTAINER_NAME": env['ubuntu_x86'],
                                           "FEDORA_X86_CONTAINER_NAME": env['fedora_x86'],
                                           "UBUNTU_AARCH_CONTAINER_NAME": env['ubuntu_aarch'],
                                           "GEN_CORPUS_IMAGE": corpus_gen_ecr_image.image_uri,
                                           "UBUNTU_X86_IMAGE": ubuntu_x86_image.image_uri,
                                           "FEDORA_X86_IMAGE": fedora_x86_image.image_uri,
                                           "UBUNTU_AARCH_IMAGE": ubuntu_aarch_image.image_uri,
                                           "UBUNTU_X86": env['ubuntu_x86'],
                                           "FEDORA_X86": env['fedora_x86'],
                                           "UBUNTU_AARCH": env['ubuntu_aarch'],
                                           "CORPUS_VOLUME": env['corpus_volume'],
                                           "CORPUS_FILE_SYSTEM_ID": file_system.file_system_id,
                                           "SUBNET_ID": subnets[0],
                                           "FARGATE_CLUSTER_NAME": env['fargate_cluster_name'],
                                           "SECURITY_GROUP_ID": security_group.security_group_id,
                                           "EXECUTION_ROLE_ARN": execution_role.role_arn,
                                           "TASK_ROLE_ARN": task_role.role_arn,
                                           "CDK_DEPLOY_REGION": env['aws_region'],
                                           "GITHUB_REPO_NAME": env['repo'],
                                           "GITHUB_REPO_OWNER": env['repo_owner'],
                                           "GITHUB_CODE_BUCKET": env['github_code_bucket'],
                                           "INTERESTING_INPUT_BUCKET": env['interesting_input_bucket']
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
                                    value=env['pub_key_secret_name'])

        git_handler_role = iam.Role(self, "Git Handler Role",
                                    assumed_by=iam.ServicePrincipal("lambda.amazonaws.com"),
                                    inline_policies=inline_policies,
                                    managed_policies=[
                                        iam.ManagedPolicy.from_aws_managed_policy_name("AmazonECS_FullAccess"),
                                        iam.ManagedPolicy.from_aws_managed_policy_name("AmazonS3FullAccess")
                                    ])

        # Set up Lambda function for handling zipping up code and running ECS tasks
        git_handler = lambda_.Function(self, "Webhook Handler",
                                       runtime=lambda_.Runtime.PYTHON_2_7,
                                       code=lambda_.Code.from_asset("GitPullS3"),
                                       handler="lambda_function.lambda_handler",
                                       environment={
                                           "GITHUB_CODE_BUCKET": env['github_code_bucket'],
                                           "PRIVATE_KEY_SECRET_NAME": env['priv_key_secret_name'],
                                           "PUBLIC_KEY_SECRET_NAME": env['pub_key_secret_name'],
                                           "FARGATE_CLUSTER_NAME": env['fargate_cluster_name'],
                                           "INTERESTING_INPUT_BUCKET": env['interesting_input_bucket'],
                                           "REPORT_BUCKET": env['report_bucket'],
                                           "UBUNTU_X86": env['ubuntu_x86'],
                                           "FEDORA_X86": env['fedora_x86'],
                                           "UBUNTU_AARCH": env['ubuntu_aarch'],
                                           "GITHUB_REPO_OWNER": env['repo_owner'],
                                           "GITHUB_REPO": env['repo'],
                                           "SECURITY_GROUP_ID": security_group.security_group_id,
                                           "SUBNET_ID": subnets[0],
                                           "COMMIT_SECRET_NAME": env['commit_secret_name']
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
            apigateway.LambdaIntegration(git_handler,
                                         proxy=False,
                                         integration_responses=[
                                             apigateway.IntegrationResponse(status_code="200")
                                         ],
                                         passthrough_behavior=apigateway.PassthroughBehavior.WHEN_NO_TEMPLATES)

        # Allow HTTP POST requests
        api.root.add_method("POST", get_webhook_integration,
                            method_responses=[
                                apigateway.MethodResponse(status_code="200")
                            ])
