def ecr_arn(ecr_repo_name, env):
    return "{}.dkr.ecr.{}.amazonaws.com/{}".format(
        env.account, env.region, ecr_repo_name
    )
