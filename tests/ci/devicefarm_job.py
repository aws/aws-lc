import boto3
import os
import requests
import string
import random
import time
import datetime
import time
import json
from cdk.util.devicefarm_util import AWS_REGION, ANDROID_TEST_NAME, ANDROID_APK, ANDROID_TEST_APK, DEVICEFARM_PROJECT, DEVICEFARM_DEVICE_POOL
from arnparse import arnparse


config = {
    "awsRegion": AWS_REGION,
    "namePrefix": ANDROID_TEST_NAME,
    "appFilePath": ANDROID_APK,
    "testPackage": ANDROID_TEST_APK,
    "projectArn": DEVICEFARM_PROJECT,
    "poolArn": DEVICEFARM_DEVICE_POOL,
}

client = boto3.client('devicefarm', region_name=AWS_REGION)

unique = config['namePrefix']
aws_region = config['awsRegion']
upload_time_limit = datetime.timedelta(minutes=30)
run_time_limit = datetime.timedelta(hours=1)

print(f"The unique identifier for this run is going to be {unique} -- all uploads will be prefixed with this.")

def upload_df_file(filename, type_, mime='application/octet-stream'):
    response = client.create_upload(projectArn=config['projectArn'],
        name = os.path.basename(filename),
        type=type_,
        contentType=mime
        )
    upload_start_time = datetime.datetime.now()
    upload_time_elapsed = datetime.timedelta(seconds=0)
    # Get the upload ARN, which we'll return later.
    upload_arn = response['upload']['arn']
    # We're going to extract the URL of the upload and use Requests to upload it
    upload_url = response['upload']['url']
    with open(filename, 'rb') as file_stream:
        print(f"Uploading {filename} to Device Farm as {response['upload']['name']}... ",end='')
        put_req = requests.put(upload_url, data=file_stream, headers={"content-type":mime})
        print(' done')
        if not put_req.ok:
            raise Exception("Couldn't upload, requests said we're not ok. Requests says: "+put_req.reason)
    while upload_time_elapsed < upload_time_limit:
        upload_time_elapsed = datetime.datetime.now() - upload_start_time
        print(f"Upload of {filename} in state {response['upload']['status']} after " + str(upload_time_elapsed))
        if response['upload']['status'] == 'FAILED':
            raise Exception("The upload failed processing. DeviceFarm says reason is: \n"+response['upload']['message'])
        if response['upload']['status'] == 'SUCCEEDED':
            break
        time.sleep(5)
        response = client.get_upload(arn=upload_arn)
    print("")
    return upload_arn

our_upload_arn = upload_df_file(config['appFilePath'], "ANDROID_APP")
our_test_package_arn = upload_df_file(config['testPackage'], 'INSTRUMENTATION_TEST_PACKAGE')
print(our_upload_arn, our_test_package_arn)
# Now that we have those out of the way, we can start the test run...
response = client.schedule_run(
    projectArn = config["projectArn"],
    appArn = our_upload_arn,
    devicePoolArn = config["poolArn"],
    name=unique,
    test = {
        "type":"INSTRUMENTATION",
        "testPackageArn": our_test_package_arn
        }
    )
run_start_time = datetime.datetime.now()
run_time_elapsed = datetime.timedelta(seconds=0)
run_arn = response['run']['arn']
project_arn_id = arnparse(run_arn).resource.split('/')[0]
run_arn_id = arnparse(run_arn).resource.split('/')[1]
run_url = "https://"+ aws_region +".console.aws.amazon.com/devicefarm/home?region=" + aws_region + "#/mobile/projects/" + \
            project_arn_id + "/runs/" + run_arn_id
print(f"\n\nRun {unique} is scheduled as arn: {run_arn} ")
print(f"Run can be observed at URL: {run_url} \n\n")
try:

    while run_time_elapsed < run_time_limit:
        run_time_elapsed = datetime.datetime.now() - run_start_time
        response = client.get_run(arn=run_arn)
        state = response['run']['status']
        if state == 'COMPLETED' or state == 'ERRORED':
            break
        else:
            print(f" Run {unique} in state {state}, total time " + str(run_time_elapsed))
            time.sleep(30)
except:
    # If something goes wrong in this process, we stop the run and exit.

    client.stop_run(arn=run_arn)
    print(f"Run stopped due to something wrong.")
    exit(1)

# Check result of device farm run.
result = response['run']['result']
print(f"Tests finished in state {result} after "+str(datetime.datetime.now() - run_start_time))
print(config['namePrefix'] + " Finished")
if result != 'PASSED':
    exit(1)
