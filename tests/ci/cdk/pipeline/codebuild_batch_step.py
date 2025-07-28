# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import builtins
import re
import typing

import jsii
from aws_cdk import (
    Duration,
    pipelines,
    aws_codepipeline_actions as cp_actions,
    aws_codebuild as codebuild,
    aws_codepipeline as codepipeline,
    aws_iam as iam,
)


@jsii.implements(pipelines.ICodePipelineActionFactory)
class CodeBuildBatchStep(pipelines.Step):
    """
    Create a CodeBuildBatchStep given shell commands and batch build settings.

    :param id: The id of the step.
    :param input: The input file set producer.
    :param action_name: Name of the action produced by this step.
    :param commands: The CodeBuild commands to be run.
    :param partial_batch_build_spec: The batch build settings for the project.
    :param role: The role to use for the CodeBuild project.
    :param timeout: Timeout of the batch build project, in minutes.
    :param env: The environment variables to use for the CodeBuild project.

    :return: A new CodeBuildBatchStep.
    """

    def __init__(
        self,
        id,
        input: pipelines.FileSet,
        action_name: str,
        commands: typing.List[str],
        partial_batch_build_spec: typing.Mapping[builtins.str, typing.Any],
        role: iam.Role,
        timeout: int = 300,
        project_description: str = None,
        env: typing.Optional[typing.Mapping[str, str]] = None,
    ):
        super().__init__(id)

        self._discover_referenced_outputs(env)

        self.input = input
        self.action_name = action_name
        self.commands = commands
        self.partial_batch_build_spec = partial_batch_build_spec
        self.role = role
        self.timeout = timeout
        self.project_description = project_description
        self.env = (
            {
                key: codebuild.BuildEnvironmentVariable(value=value)
                for key, value in env.items()
            }
            if env
            else {}
        )

    def produce_action(
        self,
        stage: codepipeline.IStage,
        options: pipelines.ProduceActionOptions,
    ) -> pipelines.CodePipelineActionFactoryResult:
        batch_build_project = codebuild.PipelineProject(
            options.scope,
            self.action_name,
            build_spec=codebuild.BuildSpec.from_object(
                {
                    "version": 0.2,
                    "batch": self.partial_batch_build_spec,
                    "phases": {"build": {"commands": self.commands}},
                }
            ),
            role=self.role,
            description=self.project_description,
            timeout=Duration.minutes(self.timeout),
        )

        batch_build_action = cp_actions.CodeBuildAction(
            action_name=self.action_name,
            input=options.artifacts.to_code_pipeline(self.input),
            run_order=options.run_order,
            project=batch_build_project,
            execute_batch_build=True,
            environment_variables=self.env,
        )

        stage.add_action(batch_build_action)

        return pipelines.CodePipelineActionFactoryResult(run_orders_consumed=1)
