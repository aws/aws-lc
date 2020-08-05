import boto3
import botocore
import os

s3_client = boto3.client('s3')
s3_resource = boto3.resource('s3')
secrets_manager = boto3.client('secretsmanager')


def lambda_handler(event, context):
    interesting_input_bucket = os.environ['INTERESTING_INPUT_BUCKET']
    report_bucket = os.environ['REPORT_BUCKET']
    commit_id = secrets_manager.get_secret_value(SecretId=os.environ['COMMIT_SECRET_NAME'])['SecretString']
    try:
        # First check to see whether all containers have finished running
        s3_resource.Object(interesting_input_bucket, '{}/{}/empty'.format(commit_id, os.environ['UBUNTU_X86'])).load()
        s3_resource.Object(interesting_input_bucket, '{}/{}/empty'.format(commit_id, os.environ['FEDORA_X86'])).load()
        s3_resource.Object(interesting_input_bucket, '{}/{}/empty'.format(commit_id, os.environ['UBUNTU_AARCH'])).load()

        # Creating report
        report_file = "/tmp/{}".format(commit_id)
        os.system('echo "Interesting Inputs Path: s3://{}/{}" > {}'.format(report_bucket, commit_id, report_file))
        s3_client.upload_file(report_file, report_bucket, commit_id)
    except botocore.exceptions.ClientError as e:
        print("All build configurations haven't finished running yet, so report hasn't been created.")
