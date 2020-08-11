# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import boto3
import botocore
import os

s3_client = boto3.client('s3')
s3_resource = boto3.resource('s3')
secrets_manager = boto3.client('secretsmanager')


def lambda_handler(event, context):
    interesting_input_bucket = os.environ['INTERESTING_INPUT_BUCKET']
    report_bucket = os.environ['REPORT_BUCKET']

    # Extract the commit id from the event that triggered the lambda function
    commit_id = event['Records'][0]['s3']['object']['key'].split('/')[0]
    try:
        build_configurations = [os.environ['UBUNTU_X86'], os.environ['FEDORA_X86'], os.environ['UBUNTU_AARCH']]
        # First check to see whether all containers have finished running
        for build_configuration in build_configurations:
            s3_resource.Object(interesting_input_bucket, '{}/{}/empty'.format(commit_id, build_configuration)).load()

        # Creating report
        report_file = "/tmp/{}".format(commit_id)
        f = open(report_file, 'w')
        # Write interesting inputs path to report file
        f.write('Interesting Inputs Path: s3://{}/{}\n'.format(interesting_input_bucket, commit_id))
        # Write whether there were any errors in any of the build configurations to the report file
        errors = ['crash', 'leak', 'timeout']
        for build_configuration in build_configurations:
            for error in errors:
                try:
                    s3_resource.Object(interesting_input_bucket, '{}/{}/{}'.format(commit_id, build_configuration, error)).load()
                    f.write('{} in {}\n'.format(error, build_configuration))
                except botocore.exceptions.ClientError as e:
                    f.write('No {} in {}\n'.format(error, build_configuration))
        f.close()
        s3_client.upload_file(report_file, report_bucket, commit_id)
    except botocore.exceptions.ClientError as e:
        print("All build configurations haven't finished running yet, so report hasn't been created.")
