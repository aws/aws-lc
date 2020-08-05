from aws_cdk import core, \
    aws_ecs as ecs, \
    aws_ec2 as ec2


# Set up of infrastructure relating to running each of the build configurations as a separate ECS task,
# on a Fargate Backend.
# This includes the following infrastructure:
# ECS cluster to run task definitions
class FuzzingStack(core.Stack):

    def __init__(self, scope: core.Construct, id: str, vpc: ec2.IVpc, env, **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # TODO: This is empty for now, but eventually, when CDK supports mounting EFS volumes for ECS containers,
        # TODO: the task definitions can go here for a better separation of functionality

        # Create ECS cluster
        cluster = ecs.Cluster(self, env['fargate_cluster_name'],
                              cluster_name=env['fargate_cluster_name'],
                              vpc=vpc)
