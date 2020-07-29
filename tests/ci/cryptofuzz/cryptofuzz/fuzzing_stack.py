from aws_cdk import core, \
    aws_ecs as ecs, \
    aws_iam as iam, \
    aws_ec2 as ec2

from util.util import EnvUtil


# Set up of infrastructure relating to running each of the build configurations as a separate ECS task,
# on a Fargate Backend.
# This includes setting up ECS-related information, and the pushing of all docker images corresponding
# to the build configurations into separate ECR repositories
class FuzzingStack(core.Stack):

    def __init__(self, scope: core.Construct, id: str, vpc: ec2.IVpc, **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Extract environment variables
        github_repo_owner = EnvUtil.get("GITHUB_REPO_OWNER", "13agupta")
        github_repo = EnvUtil.get("GITHUB_REPO", "aws-lc")
        github_code_bucket = EnvUtil.get("GITHUB_CODE_BUCKET", "github-code-bucket")
        corpus_bucket = EnvUtil.get("CORPUS_BUCKET", "cryptofuzz-corpus-bucket")
        fargate_cluster_name = EnvUtil.get("FARGATE_CLUSTER_NAME", "fargate-cryptofuzz-cluster")
        ubuntu_x86 = EnvUtil.get("UBUNTU_X86", "aws-lc-cryptofuzz-ubuntu-19-10--x86--clang-9x-sanitizer")
        fedora_x86 = EnvUtil.get("FEDORA_X86", "aws-lc-cryptofuzz-fedora-31--x86--clang-9x")
        ubuntu_aarch = EnvUtil.get("UBUNTU_AARCH", "aws-lc-cryptofuzz-ubuntu-19-10--aarch--clang-9x-sanitizer")
        interesting_input_bucket = EnvUtil.get("INTERESTING_INPUT_BUCKET", "cryptofuzz-interesting-input-bucket")
        commit_secret_name = EnvUtil.get("COMMIT_SECRET_NAME", "CommitID")
        cryptofuzz_dep_bucket = EnvUtil.get("CRYPTOFUZZ_DEP_BUCKET", "cryptofuzz-dep-bucket")

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

        # Create task definitions for each of the build configurations
        aws_lc_cryptofuzz_ubuntu_19_10__x86__clang_9x_sanitizer__task_definition = \
            ecs.TaskDefinition(self, ubuntu_x86,
                               family=ubuntu_x86,
                               compatibility=ecs.Compatibility.FARGATE,
                               cpu="4096",
                               memory_mib="30720",
                               task_role=task_role,
                               execution_role=execution_role)

        # Create linux parameters to allow docker container to run with special permissions
        aws_lc_cryptofuzz_ubuntu_19_10__x86__clang_9x_sanitizer__linux_parameters = \
            ecs.LinuxParameters(self, "aws-lc-cryptofuzz-ubuntu-19-10--x86--clang-9x_sanitizer--linux_parameters")

        aws_lc_cryptofuzz_ubuntu_19_10__x86__clang_9x_sanitizer__linux_parameters \
            .add_capabilities(ecs.Capability.SYS_PTRACE)

        # Build docker image to use for task definition
        aws_lc_cryptofuzz_ubuntu_19_10__x86__clang_9x_sanitizer__task_definition.add_container(
            ubuntu_x86,
            image=ecs.ContainerImage.from_asset("../docker_images/linux-x86/cryptofuzz_ubuntu-19.10_clang-9x_sanitizer"),
            linux_parameters=aws_lc_cryptofuzz_ubuntu_19_10__x86__clang_9x_sanitizer__linux_parameters,
            environment={
                "REPO_NAME": github_repo,
                "REPO_OWNER": github_repo_owner,
                "GITHUB_CODE_BUCKET": github_code_bucket,
                "CORPUS_BUCKET": corpus_bucket,
                "INTERESTING_INPUT_BUCKET": interesting_input_bucket,
                "COMMIT_SECRET_NAME": commit_secret_name,
                "BUILD_CONFIGURATION": ubuntu_x86,
                "CRYPTOFUZZ_DEP_BUCKET": cryptofuzz_dep_bucket
            },
            logging=ecs.LogDrivers.aws_logs(stream_prefix=ubuntu_x86)
        )

        aws_lc_cryptofuzz_fedora_31__x86__clang_9x__task_definition = \
            ecs.TaskDefinition(self, fedora_x86,
                               family=fedora_x86,
                               compatibility=ecs.Compatibility.FARGATE,
                               cpu="4096",
                               memory_mib="30720",
                               task_role=task_role,
                               execution_role=execution_role)

        # Create linux parameters to allow docker container to run with special permissions
        aws_lc_cryptofuzz_fedora_31__x86__clang_9x__linux_parameters = \
            ecs.LinuxParameters(self, "aws-lc-cryptofuzz-fedora-31--x86--clang-9x--linux_parameters")

        aws_lc_cryptofuzz_fedora_31__x86__clang_9x__linux_parameters \
            .add_capabilities(ecs.Capability.SYS_PTRACE)

        # Build docker image to use for task definition
        aws_lc_cryptofuzz_fedora_31__x86__clang_9x__task_definition.add_container(
            fedora_x86,
            image=ecs.ContainerImage.from_asset("../docker_images/linux-x86/cryptofuzz_fedora-31_clang-9x"),
            linux_parameters=aws_lc_cryptofuzz_fedora_31__x86__clang_9x__linux_parameters,
            environment={
                "REPO_NAME": github_repo,
                "REPO_OWNER": github_repo_owner,
                "GITHUB_CODE_BUCKET": github_code_bucket,
                "CORPUS_BUCKET": corpus_bucket,
                "INTERESTING_INPUT_BUCKET": interesting_input_bucket,
                "COMMIT_SECRET_NAME": commit_secret_name,
                "BUILD_CONFIGURATION": fedora_x86,
                "CRYPTOFUZZ_DEP_BUCKET": cryptofuzz_dep_bucket
            },
            logging=ecs.LogDrivers.aws_logs(stream_prefix=fedora_x86)
        )

        aws_lc_cryptofuzz_ubuntu_19_10__aarch__clang_9x_sanitizer__task_definition = \
            ecs.TaskDefinition(self, ubuntu_aarch,
                               family=ubuntu_aarch,
                               compatibility=ecs.Compatibility.FARGATE,
                               cpu="4096",
                               memory_mib="30720",
                               task_role=task_role,
                               execution_role=execution_role)

        # Create linux parameters to allow docker container to run with special permissions
        aws_lc_cryptofuzz_ubuntu_19_10__aarch__clang_9x_sanitizer__linux_parameters = \
            ecs.LinuxParameters(self, "aws-lc-cryptofuzz-ubuntu-19-10--aarch--clang-9x_sanitizer--linux_parameters")

        aws_lc_cryptofuzz_ubuntu_19_10__aarch__clang_9x_sanitizer__linux_parameters\
            .add_capabilities(ecs.Capability.SYS_PTRACE)

        # Build docker image to use for task definition
        aws_lc_cryptofuzz_ubuntu_19_10__aarch__clang_9x_sanitizer__task_definition.add_container(
            ubuntu_aarch,
            image=ecs.ContainerImage.from_asset("../docker_images/linux-aarch/cryptofuzz_ubuntu-19.10_clang-9x_sanitizer"),
            linux_parameters=aws_lc_cryptofuzz_ubuntu_19_10__aarch__clang_9x_sanitizer__linux_parameters,
            environment={
                "REPO_NAME": github_repo,
                "REPO_OWNER": github_repo_owner,
                "GITHUB_CODE_BUCKET": github_code_bucket,
                "CORPUS_BUCKET": corpus_bucket,
                "INTERESTING_INPUT_BUCKET": interesting_input_bucket,
                "COMMIT_SECRET_NAME": commit_secret_name,
                "BUILD_CONFIGURATION": ubuntu_aarch,
                "CRYPTOFUZZ_DEP_BUCKET": cryptofuzz_dep_bucket
            },
            logging=ecs.LogDrivers.aws_logs(stream_prefix=ubuntu_aarch)
        )

        # Create ECS cluster
        cluster = ecs.Cluster(self, fargate_cluster_name,
                              cluster_name=fargate_cluster_name,
                              vpc=vpc)
