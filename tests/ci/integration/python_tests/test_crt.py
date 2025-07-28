import datetime

import awscrt
import awscrt.auth
import awscrt.http
import boto3
import botocore

AWS_ACCESS_KEY_ID = "AKIDEXAMPLE"
AWS_SECRET_ACCESS_KEY = "wJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEY"
AWS_SESSION_TOKEN = None

AWS_REGION = "us-east-1"
SERVICE = "service"
DATE = datetime.datetime(
    year=2015,
    month=8,
    day=30,
    hour=12,
    minute=36,
    second=0,
    tzinfo=datetime.timezone.utc,
)

credentials_provider = awscrt.auth.AwsCredentialsProvider.new_static(
    AWS_ACCESS_KEY_ID, AWS_SECRET_ACCESS_KEY, AWS_SESSION_TOKEN
)


def test_awscrt_sigv4():
    signing_config = awscrt.auth.AwsSigningConfig(
        algorithm=awscrt.auth.AwsSigningAlgorithm.V4,
        signature_type=awscrt.auth.AwsSignatureType.HTTP_REQUEST_HEADERS,
        credentials_provider=credentials_provider,
        region=AWS_REGION,
        service=SERVICE,
        date=DATE,
    )

    http_request = awscrt.http.HttpRequest(
        method="GET",
        path="/",
        headers=awscrt.http.HttpHeaders([("Host", "example.amazonaws.com")]),
    )

    signing_result = awscrt.auth.aws_sign_request(http_request, signing_config).result()
    assert signing_result is not None
    print(f"Authorization: {signing_result.headers.get('Authorization')}")


def test_boto3():
    # make an API call to exercise SigV4 request signing in the CRT. the creds are
    # nonsense, but that's OK because we sign and make a request over the network
    # to determine that.
    client = boto3.client(
        "s3",
        aws_access_key_id=AWS_ACCESS_KEY_ID,
        aws_secret_access_key=AWS_SECRET_ACCESS_KEY,
        aws_session_token=AWS_SESSION_TOKEN,
    )
    try:
        client.list_buckets()
        assert False, "ListBuckets succeeded when it shouldn't have"
    except botocore.exceptions.ClientError as e:
        # expect it to fail due to nonsense creds
        assert "InvalidAccessKeyId" in e.response["Error"]["Code"]


if __name__ == "__main__":
    # discover test functions defined in __main__'s scope and execute them.
    for test in [test + "()" for test in globals() if test.startswith("test_")]:
        print(f"running {test}...")
        eval(test)
        print("done.")
