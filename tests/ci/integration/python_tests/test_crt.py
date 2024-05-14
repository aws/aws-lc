import boto3
import botocore
import awscrt

# make an API call to exercise SigV4 request signing in the CRT. the creds are
# nonsense, but that's OK because we sign and make a request over the network
# to determine that.
ak, sk, st = 'big', 'bad', 'wolf'
client = boto3.client(
    's3',
    aws_access_key_id=ak,
    aws_secret_access_key=sk,
    aws_session_token=st
)
try:
    client.list_buckets()
    assert False, "ListBuckets succeeded when it shouldn't have"
except botocore.exceptions.ClientError as e:
    # expect it to fail due to nonsense creds
    assert 'InvalidAccessKeyId' in e.response['Error']['Code']
