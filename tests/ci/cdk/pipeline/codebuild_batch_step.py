# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import builtins
import re
import typing
from typing import Mapping

import jsii
from aws_cdk import (
    Duration,
    pipelines,
    aws_codepipeline_actions as cp_actions,
    aws_codebuild as codebuild,
    aws_codepipeline as codepipeline,
    aws_iam as iam
)

class BatchBuildTargetOptions:
    def __init__(
            self,
            target: str,
            identifier: str = None,
            ignore_failure: bool = False,
            timeout: int = 180,
            env: Mapping[str, str] = {}
    ):
        self.target = target
        self.identifier = identifier or re.sub(r'[^a-zA-Z0-9]', '_', target)
        self.ignore_failure = ignore_failure
        self.timeout = timeout
        self.env = env

@jsii.implements(pipelines.ICodePipelineActionFactory)
class CodeBuildBatchStep(pipelines.Step):
    def __init__(self,
                 id,
                 # input: pipelines.IFileSetProducer,
                 input: pipelines.FileSet,
                 action_name: str,
                 commands: list[str],
                 role: iam.Role,
                 partial_batch_buildspec: typing.Mapping[builtins.str, typing.Any],
                 env: Mapping[str, str] = {}):
        super().__init__(id)

        self._discover_referenced_outputs(env)

        self.input = input
        self.action_name = action_name
        self.commands = commands
        self.partial_batch_buildspec = partial_batch_buildspec
        self.role = role
        self.env = {
            key: codebuild.BuildEnvironmentVariable(value=value)
            for key, value in env.items()
        }

    @jsii.member(jsii_name="produceAction")
    def produce_action(
            self,
            stage: codepipeline.IStage,
            options: pipelines.ProduceActionOptions,
    ) -> pipelines.CodePipelineActionFactoryResult:
        build_target_project = codebuild.PipelineProject(
            options.scope,
            "StartWait",
            build_spec=codebuild.BuildSpec.from_object({
                "version": 0.2,
                "batch": self.partial_batch_buildspec,
                "phases": {
                    "build": {
                        "commands": self.commands
                    }
                }
            }),
            role=self.role,
            timeout=Duration.minutes(180)
        )

        build_target_action = cp_actions.CodeBuildAction(
            action_name=self.action_name,
            # input=artifacts.to_code_pipeline(self.input.primary_output),
            input=options.artifacts.to_code_pipeline(self.input),
            run_order=options.run_order,
            project=build_target_project,
            execute_batch_build=True,
            environment_variables=self.env
        )

        stage.add_action(build_target_action)

        return pipelines.CodePipelineActionFactoryResult(
            run_orders_consumed=1
        )