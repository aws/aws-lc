# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
# Based off: https://github.com/aws-quickstart/quickstart-git2s3/blob/master/functions/source/CreateSSHKey/lambda_function.py

import traceback
import boto3
import os
import cfnresponse
from cryptography.hazmat.primitives import serialization as crypto_serialization
from cryptography.hazmat.primitives.asymmetric import rsa
from cryptography.hazmat.backends import default_backend as crypto_default_backend


def lambda_handler(event, context):
    try:
        if event['RequestType'] == 'Create':
            # Generate keys"
            new_key = rsa.generate_private_key(backend=crypto_default_backend(), public_exponent=65537, key_size=2048)
            priv_key = new_key.private_bytes(
                crypto_serialization.Encoding.PEM,
                crypto_serialization.PrivateFormat.PKCS8,
                crypto_serialization.NoEncryption()
            )
            pub_key = new_key.public_key().public_bytes(
                crypto_serialization.Encoding.OpenSSH,
                crypto_serialization.PublicFormat.OpenSSH
            )
            # Store keys as secret strings
            priv_key_secret_name = os.environ['PRIVATE_KEY_SECRET_NAME']
            secrets_manager = boto3.client('secretsmanager')
            secrets_manager.put_secret_value(SecretId=priv_key_secret_name,
                                             SecretString=priv_key)
            pub_key_secret_name = os.environ['PUBLIC_KEY_SECRET_NAME']
            secrets_manager.put_secret_value(SecretId=pub_key_secret_name,
                                             SecretString=pub_key)
            # Run ECS task that generates corpus in shared file system
            ecs = boto3.client('ecs')

            # Register task definitions for each of the build configurations and corpus generation
            build_configurations = [(os.environ['GEN_CORPUS_CONTAINER_NAME'], os.environ['GEN_CORPUS_IMAGE']),
                                    (os.environ['UBUNTU_X86'], os.environ['UBUNTU_X86_IMAGE']),
                                    (os.environ['FEDORA_X86'], os.environ['FEDORA_X86_IMAGE']),
                                    (os.environ['UBUNTU_AARCH'], os.environ['UBUNTU_AARCH_IMAGE'])]

            for (build_configuration, build_configuration_image) in build_configurations:
                ecs.register_task_definition(family=build_configuration,
                                             taskRoleArn=os.environ['TASK_ROLE_ARN'],
                                             executionRoleArn=os.environ['EXECUTION_ROLE_ARN'],
                                             networkMode='awsvpc',
                                             containerDefinitions=[
                                                 {
                                                     "name": build_configuration,
                                                     "image": build_configuration_image,
                                                     'mountPoints': [
                                                         {
                                                             'sourceVolume': os.environ['CORPUS_VOLUME'],
                                                             'containerPath': '/mount/efs'
                                                         }
                                                     ],
                                                     'environment': [
                                                         {
                                                             'name': 'REPO_NAME',
                                                             'value': os.environ['GITHUB_REPO_NAME']
                                                         },
                                                         {
                                                             'name': 'REPO_OWNER',
                                                             'value': os.environ['GITHUB_REPO_OWNER']
                                                         },
                                                         {
                                                             'name': 'GITHUB_CODE_BUCKET',
                                                             'value': os.environ['GITHUB_CODE_BUCKET']
                                                         },
                                                         {
                                                             'name': 'INTERESTING_INPUT_BUCKET',
                                                             'value': os.environ['INTERESTING_INPUT_BUCKET']
                                                         },
                                                         {
                                                             'name': 'BUILD_CONFIGURATION',
                                                             'value': build_configuration
                                                         }
                                                     ],
                                                     'linuxParameters': {
                                                         "capabilities": {
                                                             "add": [
                                                                 "SYS_PTRACE"
                                                             ]
                                                         }
                                                     },
                                                     'logConfiguration': {
                                                         'logDriver': 'awslogs',
                                                         'options': {
                                                             "awslogs-region": os.environ['CDK_DEPLOY_REGION'],
                                                             "awslogs-group": build_configuration,
                                                             "awslogs-stream-prefix": build_configuration,
                                                             "awslogs-create-group": "true"
                                                         }
                                                     }
                                                 }
                                             ],
                                             volumes=[
                                                 {
                                                     'name': os.environ['CORPUS_VOLUME'],
                                                     'efsVolumeConfiguration': {
                                                         'fileSystemId': os.environ['CORPUS_FILE_SYSTEM_ID'],
                                                         'transitEncryption': 'ENABLED'
                                                     }
                                                 }
                                             ],
                                             requiresCompatibilities=[
                                                 'FARGATE'
                                             ],
                                             cpu='4096',
                                             memory='30720')

            # Run task to create corpus
            ecs.run_task(cluster=os.environ['FARGATE_CLUSTER_NAME'],
                         launchType='FARGATE',
                         taskDefinition='generate_corpus',
                         count=1,
                         platformVersion='1.4.0',
                         networkConfiguration={
                            'awsvpcConfiguration': {
                                'subnets': [
                                    os.environ['SUBNET_ID_1'],
                                    os.environ['SUBNET_ID_2']
                                ],
                                'securityGroups': [
                                    os.environ['SECURITY_GROUP_ID']
                                ],
                                'assignPublicIp': 'ENABLED'
                            }
                        })
        else:
            pub_key = event['PhysicalResourceId']
        cfnresponse.send(event, context, cfnresponse.SUCCESS, {}, pub_key)
    except:
        traceback.print_exc()
        cfnresponse.send(event, context, cfnresponse.FAILED, {}, '')
