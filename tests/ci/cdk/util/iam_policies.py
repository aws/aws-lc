#!/usr/bin/env python3

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from util.metadata import AWS_REGION, AWS_ACCOUNT

def ec2_bm_framework_policies_in_json():
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
                    "ec2:RunInstances",
                    "ec2:TerminateInstances",
                    "ec2:CreateTags",
                    "ec2:DescribeInstances",
                    "ec2:DescribeVpcs",
                    "ec2:DescribeSecurityGroups",
                    "ec2:DescribeSubnets"
                ],
                "Resource": [
                    "*"
                ]
            }]
    }

def s3_bm_framework_policies_in_json(s3_bucket_name):
    """
    Define an IAM policy that gives some s3 permissions needed by the EC2 instances of the benchmarking framework
    """
    return {
        "Version": "2012-10-17",
        "Statement": [
            {
                "Effect": "Allow",
                "Action": [
                    "s3:ListBucket",
                    "s3:DeleteObject"
                ],
                "Resource": [
                    "arn:aws:s3:::{}".format(s3_bucket_name),
                    "arn:aws:s3:::{}/*".format(s3_bucket_name)
                ]
            }]
    }


def ssm_bm_framework_policies_in_json():
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
                    "iam:PassRole",
                    "ssm:CreateDocument",
                    "ssm:DeleteDocument",
                    "ssm:SendCommand",
                    "ssm:ListCommands",
                    "ssm:DescribeInstanceInformation"
                ],
                "Resource": [
                    "*"
                ]
            }]
    }

def code_build_batch_policy_in_json(project_ids):
    """
    Define an IAM policy statement for CodeBuild batch operation.
    :param project_ids: a list of CodeBuild project id.
    :return: an IAM policy statement in json.
    """
    resources = []
    for project_id in project_ids:
        resources.append("arn:aws:codebuild:{}:{}:project/{}*".format(AWS_REGION, AWS_ACCOUNT, project_id))
    return {
        "Version": "2012-10-17",
        "Statement": [
            {
                "Effect": "Allow",
                "Action": [
                    "codebuild:StartBuild",
                    "codebuild:StopBuild",
                    "codebuild:RetryBuild"
                ],
                "Resource": resources
            }
        ]
    }

def code_build_fuzz_policy_in_json():
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
                        "aws:RequestedRegion": [
                            AWS_REGION
                        ],
                        "cloudwatch:namespace": [
                            "AWS-LC-Fuzz"
                        ]
                    }
                }
            }
        ]
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
                "Action": [
                    "s3:Put*",
                    "s3:Get*"
                ],
                "Resource": [
                    "arn:aws:s3:::{}/*".format(s3_bucket_name)
                ]
            }
        ]
    }


def ecr_repo_arn(repo_name):
    """
    Create a ECR repository arn.
    See https://docs.aws.amazon.com/service-authorization/latest/reference/list_amazonelasticcontainerregistry.html
    :param repo_name: repository name.
    :return: arn:aws:ecr:${Region}:${Account}:repository/${RepositoryName}
    """
    ecr_arn_prefix = "arn:aws:ecr:{}:{}:repository".format(AWS_REGION, AWS_ACCOUNT)
    return "{}/{}".format(ecr_arn_prefix, repo_name)


def ecr_power_user_policy_in_json(ecr_repo_names):
    """
    Define an AWS-LC specific IAM policy statement for AWS ECR power user used to create new docker images.
    :return: an IAM policy statement in json.
    """
    ecr_arns = []
    for ecr_repo_name in ecr_repo_names:
        ecr_arns.append(ecr_repo_arn(ecr_repo_name))
    return {
        "Version": "2012-10-17",
        "Statement": [
            {
                "Effect": "Allow",
                "Action": [
                    "ecr:GetAuthorizationToken"
                ],
                "Resource": "*"
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
                    "ecr:PutImage"
                ],
                "Resource": ecr_arns
            }
        ]
    }

def aws_secrets_manager_get_secret_policy_in_json(secret_arn):
    """
    Define an IAM policy statement for getting secret value.
    :return: an IAM policy statement in json.
    """
    return {
        "Version": "2012-10-17",
        "Statement": [
            {
                "Effect": "Allow",
                "Action": [
                    "secretsmanager:GetSecretValue"
                ],
                "Resource": [
                    secret_arn
                ]
            }
        ]
    }

def aws_secrets_manager_get_secret_policy_in_json(secret_arn):
    """
    Define an IAM policy statement for getting secret value.
    :return: an IAM policy statement in json.
    """
    return {
        "Version": "2012-10-17",
        "Statement": [
            {
                "Effect": "Allow",
                "Action": [
                    "secretsmanager:GetSecretValue"
                ],
                "Resource": [
                    secret_arn
                ]
            }
        ]
    }
