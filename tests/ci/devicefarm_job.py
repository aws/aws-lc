#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

"""Run the AWS-LC Android tests on AWS Device Farm.

`start` uploads the APKs, schedules a run and waits for its result. A run can outlast the
credentials used to schedule it (GitHub Actions obtains them by role chaining, which caps a session
at one hour), so each command waits at most --max-wait-minutes. With --resumable, a run that is
still in progress when that budget runs out is left going, so that `wait` can resume it with fresh
credentials or `stop` can abandon it.

The state file records the run and exists only while a run this script scheduled may still be in
progress.
"""

import argparse
import datetime
import json
import os
import sys
import time

import boto3
import requests
from arnparse import arnparse
from botocore.exceptions import ClientError

DEFAULT_STATE_FILE = 'devicefarm-run.json'
POLL_INTERVAL_SECONDS = 30
# Uploading and processing an APK normally takes a few seconds.
UPLOAD_TIME_LIMIT = datetime.timedelta(minutes=5)
UPLOAD_REQUEST_TIMEOUT_SECONDS = 300
FINISHED_STATUSES = ('COMPLETED', 'ERRORED')
EXPIRED_CREDENTIALS_ERRORS = ('ExpiredToken', 'ExpiredTokenException')


def get_project_arn_by_name(client, project_name):
    """Look up a Device Farm project ARN by its name."""
    paginator = client.get_paginator('list_projects')
    for page in paginator.paginate():
        for project in page['projects']:
            if project['name'] == project_name:
                return project['arn']
    raise ValueError(f"Project '{project_name}' not found")


def get_device_pool_arn_by_name(client, project_arn, pool_name):
    """Look up a device pool ARN by its name within a project."""
    paginator = client.get_paginator('list_device_pools')
    for page in paginator.paginate(arn=project_arn):
        for pool in page['devicePools']:
            if pool['name'] == pool_name:
                return pool['arn']
    raise ValueError(f"Device pool '{pool_name}' not found in project")


def upload_df_file(client, project_arn, filename, type_, mime='application/octet-stream'):
    response = client.create_upload(projectArn=project_arn,
        name = os.path.basename(filename),
        type=type_,
        contentType=mime
        )
    upload_start_time = datetime.datetime.now()
    # Get the upload ARN, which we'll return later.
    upload_arn = response['upload']['arn']
    # We're going to extract the URL of the upload and use Requests to upload it
    upload_url = response['upload']['url']
    with open(filename, 'rb') as file_stream:
        print(f"Uploading {filename} to Device Farm as {response['upload']['name']}... ",end='')
        put_req = requests.put(upload_url, data=file_stream, headers={"content-type":mime},
                               timeout=UPLOAD_REQUEST_TIMEOUT_SECONDS)
        print(' done')
        if not put_req.ok:
            raise Exception("Couldn't upload, requests said we're not ok. Requests says: "+put_req.reason)
    while True:
        upload_time_elapsed = datetime.datetime.now() - upload_start_time
        print(f"Upload of {filename} in state {response['upload']['status']} after " + str(upload_time_elapsed))
        if response['upload']['status'] == 'FAILED':
            raise Exception("The upload failed processing. DeviceFarm says reason is: \n"+response['upload']['message'])
        if response['upload']['status'] == 'SUCCEEDED':
            break
        if upload_time_elapsed >= UPLOAD_TIME_LIMIT:
            raise Exception(f"Device Farm did not finish processing {filename} within {UPLOAD_TIME_LIMIT}.")
        time.sleep(5)
        response = client.get_upload(arn=upload_arn)
    print("")
    return upload_arn


def get_run_url(region, run_arn):
    project_arn_id, run_arn_id = arnparse(run_arn).resource.split('/')[:2]
    return "https://" + region + ".console.aws.amazon.com/devicefarm/home?region=" + region + \
        "#/mobile/projects/" + project_arn_id + "/runs/" + run_arn_id


def save_state(state_file, state):
    with open(state_file, 'w') as f:
        json.dump(state, f)


def load_state(state_file):
    with open(state_file) as f:
        return json.load(f)


def clear_state(state_file):
    try:
        os.remove(state_file)
    except FileNotFoundError:
        pass


def run_age(state):
    return datetime.timedelta(seconds=round(time.time() - state['scheduled_at']))


def credentials_expired(error):
    return isinstance(error, ClientError) and \
        error.response.get('Error', {}).get('Code') in EXPIRED_CREDENTIALS_ERRORS


def try_stop_run(client, state, state_file):
    """Stop the run, reporting rather than raising any failure to do so."""
    try:
        client.stop_run(arn=state['arn'])
    except ClientError as e:
        print(f"Could not stop run {state['name']}, it may still be in progress: {state['url']}\n{e}",
              file=sys.stderr)
        return
    print(f"Stopped run {state['name']}.")
    clear_state(state_file)


def wait_for_run(client, state, state_file, deadline, resumable):
    """Wait until the run finishes or time.monotonic() passes |deadline|, returning an exit code."""
    name = state['name']
    try:
        while True:
            run = client.get_run(arn=state['arn'])['run']
            status = run['status']
            if status in FINISHED_STATUSES:
                break
            if time.monotonic() >= deadline:
                if resumable:
                    print(f"Run {name} is still in state {status} after {run_age(state)}; leaving it "
                          f"running so that it can be resumed.")
                    return 0
                print(f"Run {name} did not finish within the time limit (still in state {status} after "
                      f"{run_age(state)}); stopping it.")
                try_stop_run(client, state, state_file)
                return 1
            print(f" Run {name} in state {status}, total time {run_age(state)}")
            time.sleep(max(0, min(POLL_INTERVAL_SECONDS, deadline - time.monotonic())))
    except (Exception, KeyboardInterrupt) as e:
        if credentials_expired(e):
            print(f"AWS credentials expired while waiting for run {name}, which may still be in "
                  f"progress: {state['url']}", file=sys.stderr)
            return 1
        print(f"Stopping run {name} because of an unexpected error.", file=sys.stderr)
        try_stop_run(client, state, state_file)
        raise

    clear_state(state_file)
    result = run['result']
    print(f"Tests finished in state {result} after {run_age(state)}")
    print(name + " Finished")
    return 0 if result == 'PASSED' else 1


def start(args):
    # These settings are only needed, and only set, when starting a run.
    from cdk.util.devicefarm_util import AWS_REGION, ANDROID_TEST_NAME, ANDROID_APK, ANDROID_TEST_APK, \
        DEVICEFARM_PROJECT_NAME, DEVICEFARM_DEVICE_POOL_NAME

    # The deadline includes the uploads because it bounds how long this command uses the credentials it
    # was started with, which may expire an hour after they were issued.
    deadline = time.monotonic() + args.max_wait_minutes * 60
    client = boto3.client('devicefarm', region_name=AWS_REGION)
    project_arn = get_project_arn_by_name(client, DEVICEFARM_PROJECT_NAME)
    pool_arn = get_device_pool_arn_by_name(client, project_arn, DEVICEFARM_DEVICE_POOL_NAME)

    print(f"The unique identifier for this run is going to be {ANDROID_TEST_NAME} -- all uploads will be prefixed with this.")
    app_arn = upload_df_file(client, project_arn, ANDROID_APK, 'ANDROID_APP')
    test_package_arn = upload_df_file(client, project_arn, ANDROID_TEST_APK, 'INSTRUMENTATION_TEST_PACKAGE')
    print(app_arn, test_package_arn)
    response = client.schedule_run(
        projectArn=project_arn,
        appArn=app_arn,
        devicePoolArn=pool_arn,
        name=ANDROID_TEST_NAME,
        test={
            "type": "INSTRUMENTATION",
            "testPackageArn": test_package_arn
        }
    )
    run_arn = response['run']['arn']
    state = {
        'name': ANDROID_TEST_NAME,
        'arn': run_arn,
        'region': AWS_REGION,
        'url': get_run_url(AWS_REGION, run_arn),
        'scheduled_at': time.time(),
    }
    save_state(args.state_file, state)
    print(f"\n\nRun {ANDROID_TEST_NAME} is scheduled as arn: {run_arn} ")
    print(f"Run can be observed at URL: {state['url']} \n\n")
    return wait_for_run(client, state, args.state_file, deadline, args.resumable)


def wait(args):
    if not os.path.exists(args.state_file):
        print(f"There is no Device Farm run to wait for: {args.state_file} does not exist.", file=sys.stderr)
        return 1
    state = load_state(args.state_file)
    deadline = time.monotonic() + args.max_wait_minutes * 60
    client = boto3.client('devicefarm', region_name=state['region'])
    print(f"Waiting for run {state['name']}: {state['url']}")
    return wait_for_run(client, state, args.state_file, deadline, args.resumable)


def stop(args):
    if not os.path.exists(args.state_file):
        print("There is no Device Farm run to stop.")
        return 0
    state = load_state(args.state_file)
    client = boto3.client('devicefarm', region_name=state['region'])
    status = client.get_run(arn=state['arn'])['run']['status']
    if status in FINISHED_STATUSES or status == 'STOPPING':
        print(f"Run {state['name']} is already in state {status}.")
    else:
        client.stop_run(arn=state['arn'])
        print(f"Stopped run {state['name']}: {state['url']}")
    clear_state(args.state_file)
    return 0


def main():
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument('--state-file', default=DEFAULT_STATE_FILE,
                        help=f"File that records the scheduled run (default: {DEFAULT_STATE_FILE}).")
    waiting = argparse.ArgumentParser(add_help=False)
    waiting.add_argument('--max-wait-minutes', type=int, default=60,
                         help="How long to wait for the run to finish, including any time spent uploading the "
                              "APKs (default: 60).")
    waiting.add_argument('--resumable', action='store_true',
                         help="If the run is still in progress after --max-wait-minutes, leave it running and "
                              "exit successfully instead of stopping it and failing.")

    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest='command', required=True)
    commands.add_parser('start', parents=[common, waiting],
                        help="Upload the APKs, schedule a run, and wait for it. The APK paths and Device Farm "
                             "settings are read from the environment (see kickoff_devicefarm_job.sh).")
    commands.add_parser('wait', parents=[common, waiting], help="Resume waiting for a previously scheduled run.")
    commands.add_parser('stop', parents=[common], help="Stop a previously scheduled run if it is still in progress.")
    args = parser.parse_args()
    return {'start': start, 'wait': wait, 'stop': stop}[args.command](args)


if __name__ == '__main__':
    sys.exit(main())
