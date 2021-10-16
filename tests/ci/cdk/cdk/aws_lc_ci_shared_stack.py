# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from aws_cdk import core, aws_s3 as s3
from util.metadata import AWS_LC_CI_S3_BUCKET_NAME


class AwsLcCISharedStack(core.Stack):
    """Define a stack which provide some shared AWS resources, e.g. s3."""

    def __init__(self,
                 scope: core.Construct,
                 id: str,
                 **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Define a S3 bucket to store some build artifacts.
        # This bucket is initialized to store bcm.o needed by FIPS vendor affirm build.
        s3.Bucket(self, id=AWS_LC_CI_S3_BUCKET_NAME,
          bucket_name=AWS_LC_CI_S3_BUCKET_NAME,
          block_public_access=s3.BlockPublicAccess.BLOCK_ALL)
