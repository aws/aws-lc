#!/usr/bin/env python3

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC


def ec2_policies_in_json(
    ec2_role_name, ec2_security_group_id, ec2_subnet_id, ec2_vpc_id, env
):
    """
    Define an IAM policy that gives permissions for starting, stopping, and getting details of EC2 instances and their Vpcs
    :return: an IAM policy statement in json.
    """
    return {
        "Version": "2012-10-17",
        "Statement": [
            {
                "Effect": "Allow",
                "Action": [
                    "iam:PassRole",
                    "ec2:RunInstances",
                    "ec2:TerminateInstances",
                    "ec2:CreateTags",
                    "ec2:DescribeInstances",
                ],
                "Resource": [
                    "arn:aws:iam::{}:role/{}".format(env.account, ec2_role_name),
                    "arn:aws:ec2:{}:{}:instance/*".format(env.region, env.account),
                    "arn:aws:ec2:{}::image/*".format(env.region),
                    "arn:aws:ec2:{}:{}:network-interface/*".format(
                        env.region, env.account
                    ),
                    "arn:aws:ec2:{}:{}:volume/*".format(env.region, env.account),
                    "arn:aws:ec2:{}:{}:security-group/{}".format(
                        env.region, env.account, ec2_security_group_id
                    ),
                    "arn:aws:ec2:{}:{}:subnet/{}".format(
                        env.region, env.account, ec2_subnet_id
                    ),
                    "arn:aws:ec2:{}:{}:vpc/{}".format(
                        env.region, env.account, ec2_vpc_id
                    ),
                ],
            }
        ],
    }


def ssm_policies_in_json(env):
    """
    Define an IAM policy that gives permissions to creating documents and running commands.
    :return: an IAM policy statement in json.
    """
    return {
        "Version": "2012-10-17",
        "Statement": [
            {
                "Effect": "Allow",
                "Action": [
                    "ssm:SendCommand",
                    "ssm:CreateDocument",
                    "ssm:DeleteDocument",
                    "ssm:ListCommands",
                    "ssm:DescribeInstanceInformation",
                ],
                "Resource": [
                    "arn:aws:ec2:{}:{}:instance/*".format(
                        env.region, env.account
                    ),  # Needed for ssm:SendCommand
                    "arn:aws:ssm:{}:{}:*".format(env.region, env.account),
                    "arn:aws:ssm:{}:{}:document/*".format(env.region, env.account),
                ],
            }
        ],
    }


def code_build_batch_policy_in_json(project_ids, env):
    """
    Define an IAM policy statement for CodeBuild batch operation.
    :param project_ids: a list of CodeBuild project id.
    :return: an IAM policy statement in json.
    """
    resources = []
    for project_id in project_ids:
        resources.append(
            "arn:aws:codebuild:{}:{}:project/{}*".format(
                env.region, env.account, project_id
            )
        )
    return {
        "Version": "2012-10-17",
        "Statement": [
            {
                "Effect": "Allow",
                "Action": [
                    "codebuild:StartBuild",
                    "codebuild:StopBuild",
                    "codebuild:RetryBuild",
                ],
                "Resource": resources,
            }
        ],
    }


def code_build_cloudwatch_logs_policy_in_json(log_groups):
    """
    Define an IAM policy statement for CloudWatch logs associated with CodeBuild projects.
    :param project_ids: a list of CodeBuild project id.
    :return: an IAM policy statement in json.
    """
    resources = []
    for log_group in log_groups:
        resources.append(log_group.log_group_arn)
    return {
        "Version": "2012-10-17",
        "Statement": [
            {"Effect": "Allow", "Action": ["logs:GetLogEvents"], "Resource": resources}
        ],
    }


def code_build_publish_metrics_in_json(env):
    """
    Define an IAM policy that only grants access to publish CloudWatch metrics to the current region in the same
    namespace used in the calls to PutMetricData in tests/ci/common_fuzz.sh.
    """
    return {
        "Version": "2012-10-17",
        "Statement": [
            {
                "Effect": "Allow",
                "Action": "cloudwatch:PutMetricData",
                "Resource": "*",
                "Condition": {
                    "StringEquals": {
                        "aws:RequestedRegion": [env.region],
                        "cloudwatch:namespace": ["AWS-LC-Fuzz", "AWS-LC"],
                    }
                },
            }
        ],
    }


def s3_read_write_policy_in_json(s3_bucket_name):
    """
    Define an IAM policy statement for reading and writing to S3 bucket.
    :return: an IAM policy statement in json.
    """
    return {
        "Version": "2012-10-17",
        "Statement": [
            {
                "Effect": "Allow",
                "Action": ["s3:PutObject", "s3:GetObject"],
                "Resource": ["arn:aws:s3:::{}/*".format(s3_bucket_name)],
            }
        ],
    }


def ecr_repo_arn(repo_name, env):
    """
    Create a ECR repository arn.
    See https://docs.aws.amazon.com/service-authorization/latest/reference/list_amazonelasticcontainerregistry.html
    :param repo_name: repository name.
    :return: arn:aws:ecr:${Region}:${Account}:repository/${RepositoryName}
    """
    ecr_arn_prefix = "arn:aws:ecr:{}:{}:repository".format(env.region, env.account)
    return "{}/{}".format(ecr_arn_prefix, repo_name)


def ecr_power_user_policy_in_json(ecr_repo_names, env):
    """
    Define an AWS-LC specific IAM policy statement for AWS ECR power user used to create new docker images.
    :return: an IAM policy statement in json.
    """
    ecr_arns = []
    for ecr_repo_name in ecr_repo_names:
        ecr_arns.append(ecr_repo_arn(ecr_repo_name, env))
    return {
        "Version": "2012-10-17",
        "Statement": [
            {
                "Effect": "Allow",
                "Action": ["ecr:GetAuthorizationToken"],
                "Resource": "*",
            },
            {
                "Effect": "Allow",
                "Action": [
                    "ecr:BatchCheckLayerAvailability",
                    "ecr:GetDownloadUrlForLayer",
                    "ecr:GetRepositoryPolicy",
                    "ecr:DescribeRepositories",
                    "ecr:ListImages",
                    "ecr:DescribeImages",
                    "ecr:BatchGetImage",
                    "ecr:GetLifecyclePolicy",
                    "ecr:GetLifecyclePolicyPreview",
                    "ecr:ListTagsForResource",
                    "ecr:DescribeImageScanFindings",
                    "ecr:InitiateLayerUpload",
                    "ecr:UploadLayerPart",
                    "ecr:CompleteLayerUpload",
                    "ecr:PutImage",
                ],
                "Resource": ecr_arns,
            },
        ],
    }


def device_farm_access_policy_in_json(env):
    """
    Define an IAM policy statement for Device Farm operations.
    :return: an IAM policy statement in json.
    """
    resources = []
    resources.append("arn:aws:devicefarm:{}:{}:*:*".format(env.region, env.account))
    return {
        "Version": "2012-10-17",
        "Statement": [
            {
                "Sid": "ViewProjectInfo",
                "Effect": "Allow",
                "Action": [
                    "devicefarm:CreateUpload",
                    "devicefarm:GetUpload",
                    "devicefarm:GetRun",
                    "devicefarm:ScheduleRun",
                    "devicefarm:StopRun",
                    "devicefarm:ListArtifacts",
                    "devicefarm:ListJobs",
                    "devicefarm:ListSuites",
                    "devicefarm:ListTests",
                ],
                "Resource": resources,
            }
        ],
    }
