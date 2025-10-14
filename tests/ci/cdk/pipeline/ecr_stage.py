import typing

from aws_cdk import (
    Stage,
    Environment,
    Stack,
    pipelines,
)
from cdk.ecr_stack import PrivateEcrStackV2
from constructs import Construct

class EcrStage(Stage):
    """Define a stack of IAM role to allow cross-account deployment"""

    def __init__(
        self,
        scope: Construct,
        id: str,
        pipeline_environment: typing.Union[Environment, typing.Dict[str, typing.Any]],
        deploy_environment: typing.Union[Environment, typing.Dict[str, typing.Any]],
        **kwargs,
    ):
        super().__init__(
            scope,
            id,
            env=pipeline_environment,
            **kwargs,
        )

        PrivateEcrStackV2(self, "aws-lc-private-ecr-stack", env=deploy_environment, **kwargs)

    @property
    def stacks(self):
        return [child for child in self.node.children if isinstance(child, Stack)]
    
    def add_stage_to_wave(self, wave: pipelines.Wave):
        wave.add_stage(self)
