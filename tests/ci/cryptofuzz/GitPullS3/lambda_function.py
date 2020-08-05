#  Copyright 2016 Amazon Web Services, Inc. or its affiliates. All Rights Reserved.
#  This file is licensed to you under the AWS Customer Agreement (the "License").
#  You may not use this file except in compliance with the License.
#  A copy of the License is located at http://aws.amazon.com/agreement/ .
#  This file is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or implied.
#  See the License for the specific language governing permissions and limitations under the License.

from pygit2 import Keypair, discover_repository, Repository, clone_repository, RemoteCallbacks
from boto3 import client
import os
import stat
import shutil
from zipfile import ZipFile
import logging

# If true the function will not include .git folder in the zip
exclude_git = False

# If true the function will delete all files at the end of each invocation, useful if you run into storage space
# constraints, but will slow down invocations as each invoke will need to checkout the entire repo
cleanup = False

key = 'enc_key'

logger = logging.getLogger()
logger.setLevel(logging.INFO)
logger.handlers[0].setFormatter(logging.Formatter('[%(asctime)s][%(levelname)s] %(message)s'))
logging.getLogger('boto3').setLevel(logging.ERROR)
logging.getLogger('botocore').setLevel(logging.ERROR)

s3 = client('s3')
kms = client('kms')
secrets_manager = client('secretsmanager')
ecs = client('ecs')


def write_key(filename, contents):
    logger.info('Writing keys to /tmp/...')
    mode = stat.S_IRUSR | stat.S_IWUSR
    umask_original = os.umask(0)
    try:
        handle = os.fdopen(os.open(filename, os.O_WRONLY | os.O_CREAT, mode), 'w')
    finally:
        os.umask(umask_original)
    handle.write(contents + '\n')
    handle.close()


def get_keys(update=False):
    if not os.path.isfile('/tmp/id_rsa') or not os.path.isfile('/tmp/id_rsa.pub') or update:
        logger.info('Keys not found on Lambda container, fetching from Secrets Manager...')
        pub_key_secret_name = os.environ['PUBLIC_KEY_SECRET_NAME']
        priv_key_secret_name = os.environ['PRIVATE_KEY_SECRET_NAME']
        privkey = secrets_manager.get_secret_value(SecretId=priv_key_secret_name)
        pubkey = secrets_manager.get_secret_value(SecretId=pub_key_secret_name)
        logger.info('pub_key %s', pubkey)
        logger.info('priv_key %s', privkey)
        privkey = privkey['SecretString']
        pubkey = pubkey['SecretString']
        write_key('/tmp/id_rsa', privkey)
        write_key('/tmp/id_rsa.pub', pubkey)
    return Keypair('git', '/tmp/id_rsa.pub', '/tmp/id_rsa', '')


def init_remote(repo, name, url):
    remote = repo.remotes.create(name, url, '+refs/*:refs/*')
    return remote


def create_repo(repo_path, remote_url, creds):
    if os.path.exists(repo_path):
        logger.info('Cleaning up repo path...')
        shutil.rmtree(repo_path)
    repo = clone_repository(remote_url, repo_path, callbacks=creds)

    return repo


def pull_repo(repo, branch_name, remote_url, creds):
    remote_exists = False
    for r in repo.remotes:
        if r.url == remote_url:
            remote_exists = True
            remote = r
    if not remote_exists:
        remote = repo.create_remote('origin', remote_url)
    logger.info('Fetching and merging changes from %s branch %s', remote_url, branch_name)
    remote.fetch(callbacks=creds)
    if(branch_name.startswith('tags/')):
        ref = 'refs/' + branch_name
    else:
        ref = 'refs/remotes/origin/' + branch_name
    remote_branch_id = repo.lookup_reference(ref).target
    repo.checkout_tree(repo.get(remote_branch_id))
    repo.head.set_target(remote_branch_id)
    return repo


def zip_repo(repo_path, repo_name):
    logger.info('Creating zipfile...')
    zf = ZipFile('/tmp/'+repo_name.replace('/', '_')+'.zip', 'w')
    for dirname, subdirs, files in os.walk(repo_path):
        if exclude_git:
            try:
                subdirs.remove('.git')
            except ValueError:
                pass
        zdirname = dirname[len(repo_path)+1:]
        zf.write(dirname, zdirname)
        for filename in files:
            zf.write(os.path.join(dirname, filename), os.path.join(zdirname, filename))
    zf.close()
    return '/tmp/'+repo_name.replace('/', '_')+'.zip'


def push_s3(filename, repo_name, outputbucket):
    s3key = '%s/%s' % (repo_name, filename.replace('/tmp/', ''))
    logger.info('pushing zip to s3://%s/%s' % (outputbucket, s3key))
    data = open(filename, 'rb')
    s3.put_object(Bucket=outputbucket, Body=data, Key=s3key)
    logger.info('Completed S3 upload...')


def lambda_handler(event, context):
    logger.info("Event %s", event)
    outputbucket = os.environ['GITHUB_CODE_BUCKET']
    commit_id = event['after']
    secrets_manager.put_secret_value(SecretId=os.environ['COMMIT_SECRET_NAME'],
                                     SecretString=commit_id)

    path = '/tmp/{}/'.format(commit_id)
    command = 'mkdir {}'.format(path)
    os.system(command)
    s3.put_object(Bucket=os.environ['INTERESTING_INPUT_BUCKET'],
                  Key=path)

    # GitHub
    full_name = event['repository']['full_name']

    # GitHub publish event
    if ('action' in event and event['action'] == 'published'):
        branch_name = 'tags/%s' % event['release']['tag_name']
        repo_name = full_name + '/release'
    else:
        repo_name = full_name
        try:
            # branch names should contain [name] only, tag names - "tags/[name]"
            branch_name = event['ref'].replace('refs/heads/', '').replace('refs/tags/', 'tags/')
        except KeyError:
            branch_name = 'master'

    # GitHub
    remote_url = event['repository']['ssh_url']
    repo_path = '/tmp/%s' % repo_name
    creds = RemoteCallbacks(credentials=get_keys(), )
    try:
        repository_path = discover_repository(repo_path)
        repo = Repository(repository_path)
        logger.info('found existing repo, using that...')
    except Exception:
        logger.info('creating new repo for %s in %s' % (remote_url, repo_path))
        repo = create_repo(repo_path, remote_url, creds)
    pull_repo(repo, branch_name, remote_url, creds)
    zipfile = zip_repo(repo_path, repo_name)
    push_s3(zipfile, repo_name, outputbucket)

    # Run tasks corresponding to each of the build configurations
    ecs.run_task(cluster=os.environ['FARGATE_CLUSTER_NAME'],
                 launchType='FARGATE',
                 taskDefinition=os.environ['UBUNTU_X86'],
                 count=1,
                 platformVersion='1.4.0',
                 networkConfiguration={
                     'awsvpcConfiguration': {
                         'subnets': [
                             os.environ['SUBNET_ID']
                         ],
                         'securityGroups': [
                             os.environ['SECURITY_GROUP_ID']
                         ],
                         'assignPublicIp': 'ENABLED'
                     }
                 },
                 overrides={
                     'containerOverrides': [
                         {
                             'name': os.environ['UBUNTU_X86'],
                             'environment': [
                                 {
                                     'name': 'COMMIT_ID',
                                     'value': commit_id
                                 }
                             ]
                         }
                     ]
                 })

    ecs.run_task(cluster=os.environ['FARGATE_CLUSTER_NAME'],
                 launchType='FARGATE',
                 taskDefinition=os.environ['FEDORA_X86'],
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
                 overrides={
                     'containerOverrides': [
                         {
                             'name': os.environ['FEDORA_X86'],
                             'environment': [
                                 {
                                     'name': 'COMMIT_ID',
                                     'value': secrets_manager.get_secret_value(
                                         SecretId=os.environ['COMMIT_SECRET_NAME'])
                                 }
                             ]
                         }
                     ]
                 })

    ecs.run_task(cluster=os.environ['FARGATE_CLUSTER_NAME'],
                 launchType='FARGATE',
                 taskDefinition=os.environ['UBUNTU_AARCH'],
                 count=1,
                 platformVersion='1.4.0',
                 networkConfiguration={
                     'awsvpcConfiguration': {
                         'subnets': [
                             os.environ['SUBNET_ID']
                         ],
                         'securityGroup': [
                             os.environ['SECURITY_GROUP_ID']
                         ],
                         'assignPublicIp': 'ENABLED'
                     }
                 },
                 overrides={
                     'containerOverrides': [
                         {
                             'name': os.environ['UBUNTU_AARCH'],
                             'environment': [
                                 {
                                     'name': 'COMMIT_ID',
                                     'value': secrets_manager.get_secret_value(SecretId=os.environ['COMMIT_SECRET_NAME'])
                                 }
                             ]
                         }
                     ]
                 })
    if cleanup:
        logger.info('Cleanup Lambda container...')
        shutil.rmtree(repo_path)
        os.remove(zipfile)
        os.remove('/tmp/id_rsa')
        os.remove('/tmp/id_rsa.pub')
    return 'Successfully updated %s' % repo_name
