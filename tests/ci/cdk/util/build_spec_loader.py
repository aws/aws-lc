#!/usr/bin/env python3

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

from aws_cdk import aws_codebuild as codebuild
from util.metadata import PROD_ACCOUNT, PROD_REGION
import tempfile


class BuildSpecLoader(object):
    """Responsible for loading the BuildSpec yml file as python object."""

    @staticmethod
    def load(file_path, env):
        """
        Used to load yml file and replace some placeholders if needed.
        :param file_path: path to the yml file.
        :return: python object.
        """
        # Indicate if the BuildSpec files can be automatically loaded without manual deployment.
        can_autoload = (env.account == PROD_ACCOUNT) and (env.region == PROD_REGION)

        # If the deployment uses team account, the change of batch BuildSpec file is loaded automatically without deployment.
        # else, the change will require manual deployment via CDK command.
        if can_autoload:
            return codebuild.BuildSpec.from_source_filename(
                "tests/ci/cdk/{}".format(file_path)
            )
        # TODO(CryptoAlg-1276): remove below when the batch BuildSpec supports the env variable of account and region.
        placeholder_map = {
            PROD_ACCOUNT: env.account,
            PROD_REGION: env.region,
        }
        with open(file_path) as original_file:
            file_text = original_file.read()
            for key in placeholder_map.keys():
                file_text = file_text.replace(key, placeholder_map[key])
            with tempfile.NamedTemporaryFile(mode="w+", delete=False) as temp_file:
                temp_file.write(file_text)
                return codebuild.BuildSpec.from_asset(temp_file.name)
