# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import re
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
from constructs import Construct


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
class CodeBuildRunStep(pipelines.Step):
    def __init__(self,
                 id,
                 name_prefix,
                 # input: pipelines.IFileSetProducer,
                 input: pipelines.FileSet,
                 stacks: list[str],
                 role: iam.Role,
                 platform: str = "",
                 build_targets: list[BatchBuildTargetOptions] = None,
                 max_retry: int = 0,
                 env: Mapping[str, str] = {}):
        super().__init__(id)

        self._discover_referenced_outputs(env)

        self.name_prefix = name_prefix
        self.input = input
        self.platform = platform
        self.stacks = stacks
        self.build_targets = build_targets
        self.role = role
        self.max_retry = max_retry
        self.env = {
            key: codebuild.BuildEnvironmentVariable(value=value)
            for key, value in env.items()
        }

    @jsii.member(jsii_name="produceAction")
    def produce_action(self,
                       stage: codepipeline.IStage,
                       options: pipelines.ProduceActionOptions,
                       ) -> pipelines.CodePipelineActionFactoryResult:
        batch_build_jobs = [
            {
                "identifier": options.identifier,
                "ignore-failure": options.ignore_failure,
                "env": {
                    "variables": {
                        "PROJECT": options.target,
                        "TIMEOUT": options.timeout,
                        **options.env,
                    }
                }
            }
            for options in self.build_targets
        ]

        build_target_project = codebuild.PipelineProject(
            options.scope,
            "StartWait",
            build_spec=codebuild.BuildSpec.from_object({
                "version": 0.2,
                "batch": {
                    "build-list": batch_build_jobs
                },
                "phases": {
                    "build": {
                        "commands": [
                            "cd tests/ci/cdk/pipeline/scripts",
                            "chmod +x build_target.sh",
                            "./build_target.sh --build-type ci --project ${PROJECT} --max-retry ${MAX_RETRY} --timeout ${TIMEOUT}"
                        ]
                    }
                }
            }),
            role=self.role,
            timeout=Duration.minutes(180)
        )

        build_target_action = cp_actions.CodeBuildAction(
            # action_name=f"{self.name_prefix}.StartWait",
            action_name="StartWait",
            # input=artifacts.to_code_pipeline(self.input.primary_output),
            input=options.artifacts.to_code_pipeline(self.input),
            run_order=options.run_order + 1,
            project=build_target_project,
            execute_batch_build=True,
            environment_variables={
                **self.env,
                "MAX_RETRY": codebuild.BuildEnvironmentVariable(value=self.max_retry),
            },
        )

        stage.add_action(build_target_action)

        return pipelines.CodePipelineActionFactoryResult(
            run_orders_consumed=1
        )