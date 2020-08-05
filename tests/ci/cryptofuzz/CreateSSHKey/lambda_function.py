#  Copyright 2016 Amazon Web Services, Inc. or its affiliates. All Rights Reserved.
#  This file is licensed to you under the AWS Customer Agreement (the "License").
#  You may not use this file except in compliance with the License.
#  A copy of the License is located at http://aws.amazon.com/agreement/ .
#  This file is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or implied.
#  See the License for the specific language governing permissions and limitations under the License.

import traceback
import boto3
import os
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
            resp_corpus = ecs.register_task_definition(family='generate_corpus',
                                                       executionRoleArn=os.environ['EXECUTION_ROLE_ARN'],
                                                       networkMode='awsvpc',
                                                       containerDefinitions=[
                                                           {
                                                               "name": os.environ['GEN_CORPUS_CONTAINER_NAME'],
                                                               "image": os.environ['GEN_CORPUS_IMAGE'],
                                                               'mountPoints': [
                                                                   {
                                                                       'sourceVolume': os.environ['CORPUS_VOLUME'],
                                                                       'containerPath': '/mount/efs'
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
                                                                       "awslogs-group": 'generate_corpus',
                                                                       "awslogs-stream-prefix": 'generate_corpus',
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

            resp_ubuntu_x86 = ecs.register_task_definition(family=os.environ['UBUNTU_X86'],
                                                           taskRoleArn=os.environ['TASK_ROLE_ARN'],
                                                           executionRoleArn=os.environ['EXECUTION_ROLE_ARN'],
                                                           networkMode='awsvpc',
                                                           containerDefinitions=[
                                                               {
                                                                   "name": os.environ['UBUNTU_X86'],
                                                                   "image": os.environ['UBUNTU_X86_IMAGE'],
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
                                                                           'value': os.environ['UBUNTU_X86']
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
                                                                           "awslogs-group": os.environ['UBUNTU_X86'],
                                                                           "awslogs-stream-prefix": os.environ['UBUNTU_X86'],
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

            resp_fedora_x86 = ecs.register_task_definition(family=os.environ['FEDORA_X86'],
                                                           taskRoleArn=os.environ['TASK_ROLE_ARN'],
                                                           executionRoleArn=os.environ['EXECUTION_ROLE_ARN'],
                                                           networkMode='awsvpc',
                                                           containerDefinitions=[
                                                               {
                                                                   "name": os.environ['FEDORA_X86'],
                                                                   "image": os.environ['FEDORA_X86_IMAGE'],
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
                                                                           'value': os.environ[
                                                                               'INTERESTING_INPUT_BUCKET']
                                                                       },
                                                                       {
                                                                           'name': 'COMMIT_SECRET_NAME',
                                                                           'value': os.environ['COMMIT_SECRET_NAME']
                                                                       },
                                                                       {
                                                                           'name': 'BUILD_CONFIGURATION',
                                                                           'value': os.environ['FEDORA_X86']
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
                                                                           "awslogs-group": os.environ['FEDORA_X86'],
                                                                           "awslogs-stream-prefix": os.environ['FEDORA_X86'],
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

            resp_ubuntu_aarch = ecs.register_task_definition(family=os.environ['UBUNTU_AARCH'],
                                                             taskRoleArn=os.environ['TASK_ROLE_ARN'],
                                                             executionRoleArn=os.environ['EXECUTION_ROLE_ARN'],
                                                             networkMode='awsvpc',
                                                             containerDefinitions=[{
                                                                 "name": os.environ['UBUNTU_AARCH'],
                                                                 "image": os.environ['UBUNTU_AARCH_IMAGE'],
                                                                 'mountPoints': [{
                                                                     'sourceVolume': os.environ['CORPUS_VOLUME'],
                                                                     'containerPath': '/mount/efs'
                                                                 }],
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
                                                                           'name': 'COMMIT_SECRET_NAME',
                                                                           'value': os.environ['COMMIT_SECRET_NAME']
                                                                       },
                                                                       {
                                                                           'name': 'BUILD_CONFIGURATION',
                                                                           'value': os.environ['UBUNTU_AARCH']
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
                                                                         "awslogs-group": os.environ['UBUNTU_AARCH'],
                                                                         "awslogs-stream-prefix": os.environ[
                                                                             'UBUNTU_AARCH'],
                                                                         "awslogs-create-group": "true"
                                                                     }
                                                                 }
                                                             }],
                                                             volumes=[{
                                                                 'name': os.environ['CORPUS_VOLUME'],
                                                                 'efsVolumeConfiguration': {
                                                                     'fileSystemId': os.environ['CORPUS_FILE_SYSTEM_ID'],
                                                                     'transitEncryption': 'ENABLED'
                                                                 }
                                                             }],
                                                             requiresCompatibilities=[
                                                                 'FARGATE'
                                                             ],
                                                             cpu='4096',
                                                             memory='30720')

            ecs.run_task(cluster=os.environ['FARGATE_CLUSTER_NAME'],
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
                                    os.environ['SECURITY_GROUP_ID']
                                ],
                                'assignPublicIp': 'ENABLED'
                            }
                        },
                        )
        else:
            pub_key = event['PhysicalResourceId']
    except:
        traceback.print_exc()
