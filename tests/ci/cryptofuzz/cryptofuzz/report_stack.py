# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from aws_cdk import core, \
    aws_s3 as s3, \
    aws_lambda as lambda_, \
    aws_s3_notifications as s3_notifications, \
    aws_iam as iam


# This stack contains all the infrastructure relating to the report and its generation.
# This includes the following infrastructure:
# S3 buckets for interesting inputs, and reports
# Lambda function to create the report, to trigger after build configurations are finished
# (And associated IAM policies/roles)
# S3 bucket trigger going to lambda function that creates the report
class ReportStack(core.Stack):

    def __init__(self, scope: core.Construct, id: str, env, **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Create the S3 bucket for the reports
        s3_report_bucket = s3.Bucket(self, env['report_bucket'],
                                     bucket_name=env['report_bucket'])

        # Create the S3 bucket for the interesting inputs
        s3_interesting_input_bucket = s3.Bucket(self, env['interesting_input_bucket'],
                                                bucket_name=env['interesting_input_bucket'])

        # Create lambda that generates the reports after fuzzing is complete
        report_lambda = lambda_.Function(self, "report-lambda",
                                         runtime=lambda_.Runtime.PYTHON_3_7,
                                         code=lambda_.Code.from_asset("ReportFunction"),
                                         handler="lambda_function.lambda_handler",
                                         environment={
                                             "REPORT_BUCKET": env['report_bucket'],
                                             "INTERESTING_INPUT_BUCKET": env['interesting_input_bucket'],
                                             "UBUNTU_X86": env['ubuntu_x86'],
                                             "FEDORA_X86": env['fedora_x86'],
                                             "UBUNTU_AARCH": env['ubuntu_aarch']
                                         },
                                         timeout=core.Duration.minutes(5))

        # Add event notification so that S3 bucket can trigger report lambda when interesting inputs are updated
        s3_interesting_input_bucket.add_event_notification(s3.EventType.OBJECT_CREATED,
                                                           s3_notifications.LambdaDestination(report_lambda))

        # Granting S3 permissions to the report lambda
        s3_report_bucket.grant_read_write(report_lambda)
        s3_interesting_input_bucket.grant_read_write(report_lambda)

        # Add S3 buckets trigger permissions to the report lambda resource policy
        report_lambda.add_permission(id="S3 Invoke Access",
                                     principal=iam.ServicePrincipal("s3.amazonaws.com"),
                                     source_arn=s3_interesting_input_bucket.bucket_arn,
                                     source_account=env['aws_account'])
