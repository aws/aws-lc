from util.metadata import AWS_ACCOUNT, AWS_REGION


def ecr_arn(ecr_repo_name):
    return "{}.dkr.ecr.{}.amazonaws.com/{}".format(AWS_ACCOUNT, AWS_REGION, ecr_repo_name)
