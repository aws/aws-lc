#  Copyright 2016 Amazon Web Services, Inc. or its affiliates. All Rights Reserved.
#  This file is licensed to you under the AWS Customer Agreement (the "License").
#  You may not use this file except in compliance with the License.
#  A copy of the License is located at http://aws.amazon.com/agreement/ .
#  This file is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or implied.
#  See the License for the specific language governing permissions and limitations under the License.

import cfnresponse
import traceback
import boto3
import os
from cryptography.hazmat.primitives import serialization as crypto_serialization
from cryptography.hazmat.primitives.asymmetric import rsa
from cryptography.hazmat.backends import default_backend as crypto_default_backend


def lambda_handler(event,context):
    try:
        if event['RequestType'] == 'Create':
            # Generate keys
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
            # Print results
            print(priv_key)
            print(pub_key)
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
            resp = ecs.register_task_definition(family='generate_corpus',
                                                containerDefinitions=[
                                                    {
                                                        "name": os.environ['GEN_CORPUS_CONTAINER_NAME'],
                                                        "image": os.environ['GEN_CORPUS_IMAGE'],
                                                        'mountPoints': [
                                                            {
                                                                'sourceVolume': os.environ['CORPUS_VOLUME'],
                                                                'containerPath': '/mount/efs'
                                                            }
                                                        ]
                                                    }
                                                ],
                                                logDriver='awslogs',
                                                volumes=[
                                                    {
                                                        'name': os.environ['CORPUS_VOLUME'],
                                                        'efsVolumeConfiguration': {
                                                            'fileSystemId': os.environ['CORPUS_FILE_SYSTEM_ID'],
                                                            'transitEncryption': 'ENABLED'
                                                        }
                                                    }
                                                ],
                                                requiredCompatibilities=[
                                                    'Fargate'
                                                ],
                                                cpu='4096',
                                                memory='30720')
            ecs.RunTask(cluster=os.environ['FARGATE_CLUSTER_NAME'],
                        launchType='FARGATE',
                        taskDefinition='generate_corpus',
                        count=1,
                        platformVersion='1.4.0',
                        networkConfiguration={
                            'awsvpcConfiguration': {
                                'subnets': [
                                    os.environ["SUBNET_ID"]
                                ],
                                'securityGroups': [
                                    os.environ['SECURITY_GROUP_NAME']
                                ],
                                'assignPublicIp': 'ENABLED'
                            }
                        },
                        )
        else:
            pub_key = event['PhysicalResourceId']
        cfnresponse.send(event, context, cfnresponse.SUCCESS, {}, pub_key)
    except:
        traceback.print_exc()
        cfnresponse.send(event, context, cfnresponse.FAILED, {}, '')
