import boto3
import botocore
import os

s3 = boto3.client('s3')
secrets_manager = boto3.client('secretsmanager')


def download_dir(prefix, local, bucket, client=s3):
    """
    params:
    - prefix: pattern to match in s3
    - local: local path to folder in which to place files
    - bucket: s3 bucket with target contents
    - client: initialized s3 client object
    """
    keys = []
    dirs = []
    next_token = ''
    base_kwargs = {
        'Bucket': bucket,
        'Prefix': prefix,
    }
    while next_token is not None:
        kwargs = base_kwargs.copy()
        if next_token != '':
            kwargs.update({'ContinuationToken': next_token})
        results = client.list_objects_v2(**kwargs)
        contents = results.get('Contents')
        for i in contents:
            k = i.get('Key')
            if k[-1] != '/':
                keys.append(k)
            else:
                dirs.append(k)
        next_token = results.get('NextContinuationToken')
    for d in dirs:
        dest_pathname = os.path.join(local, d)
        if not os.path.exists(os.path.dirname(dest_pathname)):
            os.makedirs(os.path.dirname(dest_pathname))
    for k in keys:
        dest_pathname = os.path.join(local, k)
        if not os.path.exists(os.path.dirname(dest_pathname)):
            os.makedirs(os.path.dirname(dest_pathname))
        client.download_file(bucket, k, dest_pathname)

def lambda_handler(event, context):
    for record in event['Records']:
        interesting_input_bucket = os.environ['INTERESTING_INPUT_BUCKET']
        report_bucket = os.environ['REPORT_BUCKET']
        corpus_bucket = os.environ['CORPUS_BUCKET']
        commit_id = secrets_manager.get_secret_value(SecretId=os.environ['COMMIT_SECRET_NAME'])
        try:
            # First check to see whether all containers have finished running
            s3.Object(interesting_input_bucket, '{}/{}/'.format(commit_id, os.environ['UBUNTU_X86'])).load()
            s3.Object(interesting_input_bucket, '{}/{}/'.format(commit_id, os.environ['FEDORA_X86'])).load()
            # s3.Object(interesting_input_bucket, '{}/{}/'.format(commit_id, os.environ['UBUNTU_AARCH'])).load()

            # Creating report
            report_file = "/tmp/{}".format(commit_id)
            os.system('echo "Interesting Inputs Path: s3://{}/{}" > {}'.format(report_bucket, commit_id, report_file))
            s3.upload_file(report_file, report_bucket, commit_id)
        except botocore.exceptions.ClientError as e:
            print("All build configurations haven't finished running yet, so report hasn't been created.")
