#!/usr/bin/env python3

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from util.metadata import AWS_REGION, AWS_ACCOUNT


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


def ecr_pull_only_policy_in_json(ecr_repo_name):
    """
    Define an AWS-LC specific IAM policy statement used to pull Docker images from ECR repo.
    Reference:
      https://docs.aws.amazon.com/service-authorization/latest/reference/list_amazonelasticcontainerregistry.html
    :param ecr_repo_name: repository name.
    :return: an IAM policy statement in json.
    """
    return {
        "Version": "2012-10-17",
        "Statement": [
            {
                "Effect": "Allow",
                "Action": [
                    "ecr:BatchCheckLayerAvailability",
                    "ecr:GetDownloadUrlForLayer",
                    "ecr:BatchGetImage",
                ],
                "Resource": ecr_repo_arn(ecr_repo_name)
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
