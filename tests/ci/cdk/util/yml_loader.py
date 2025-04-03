#!/usr/bin/env python3

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC


import typing
import yaml


class YmlLoader(object):
    """Responsible for loading yml file as python object."""

    @staticmethod
    def load(
        file_path, placeholder_map: typing.Optional[typing.Mapping[str, str]] = None
    ):
        """
        Used to load yml file and replace some placeholders if needed.
        :param file_path: path to the yml file.
        :param placeholder_map: a mapping from placeholder to corresponding value.
        :return: python object.
        """
        placeholder_map = placeholder_map or {}
        with open(file_path) as file:
            file_text = file.read()
            for key in placeholder_map.keys():
                file_text = file_text.replace(key, placeholder_map[key])
            return yaml.safe_load(file_text)
