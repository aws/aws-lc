# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import pathlib
import typing
from typing import Dict, Optional

from aws_cdk import (
    aws_codebuild as codebuild,
    aws_ec2 as ec2,
    Environment,
    Stack,
    Tags
)
from constructs import Construct

from util.fleet_config_loader import (
    FleetConfigLoader,
    FleetConfiguration,
    FleetConfigurationFile,
    validate_fleet_config
)


class CodeBuildFleet(Construct):
    """A construct that creates and manages a single CodeBuild fleet with scaling configuration."""
    
    def __init__(
        self,
        scope: Construct,
        construct_id: str,
        fleet_config: FleetConfiguration,
        **kwargs
    ) -> None:
        super().__init__(scope, construct_id, **kwargs)
        
        self.fleet_config = fleet_config
        self.fleet_name = fleet_config.name
        
        # Create the CodeBuild fleet
        self.fleet = self._create_fleet()
        
        # Configure auto-scaling if enabled
        if fleet_config.scaling_configuration.enabled:
            self._configure_scaling()
        
        # Apply tags
        self._apply_tags()
    
    def _create_fleet(self) -> codebuild.IFleet:
        """Create the CodeBuild fleet based on configuration."""
        fleet_props = {
            "fleet_name": self.fleet_name,
            "base_capacity": self.fleet_config.base_capacity,
            "environment_type": self._get_environment_type(),
        }
        
        # Add compute configuration based on type
        compute_config = self._get_compute_configuration()
        fleet_props.update(compute_config)
        
        fleet_props["overflow_behavior"] = codebuild.FleetOverflowBehavior.QUEUE

        fleet = codebuild.Fleet(self, f"{self.fleet_name}-Fleet", **fleet_props)
                
        return fleet
    
    def _get_environment_type(self) -> str:
        """Get the CDK environment type from configuration."""
        return codebuild.EnvironmentType[self.fleet_config.environment_type]
    
    def _get_compute_configuration(self) -> Dict[str, typing.Any]:
        """Get the compute configuration for the fleet based on type."""
        config = self.fleet_config
        
        if config.compute_type:
            # Fixed compute type (e.g., BUILD_GENERAL1_SMALL)
            return {
                "compute_type": codebuild.FleetComputeType[config.compute_type],
            }
        elif config.custom_instance_type:
            # Custom instance type (e.g., m5.large)
            return {
                "compute_type": codebuild.FleetComputeType.CUSTOM_INSTANCE_TYPE,
                "compute_configuration": {
                    "instance_type": ec2.InstanceType(config.custom_instance_type),
                },
            }
        elif config.attribute_based_compute:
            # Attribute-based compute with specific requirements
            attr = config.attribute_based_compute
            return {
                "compute_type": codebuild.FleetComputeType.ATTRIBUTE_BASED,  # Base type for attribute-based
                "compute_configuration": {
                    "vcpus": attr.vcpus,
                    "memory": attr.memory,
                    "disk": attr.storage
                },
            }
        else:
            raise ValueError(f"No compute type specified for fleet {self.fleet_name}")
    
    def _configure_scaling(self) -> None:
        """Configure auto-scaling for the fleet."""
        scaling_config = self.fleet_config.scaling_configuration
        
        if not scaling_config.enabled:
            return
        
        fleet_cn: codebuild.CfnFleet = self.fleet.node.default_child

        optional_props = {}

        if scaling_config.utilization_rate:
            optional_props["target_tracking_scaling_configs"] = \
                [codebuild.CfnFleet.TargetTrackingScalingConfigurationProperty(
                    metric_type="FLEET_UTILIZATION_RATE",
                    target_value=scaling_config.utilization_rate)]

        scaling_configuration_input = codebuild.CfnFleet.ScalingConfigurationInputProperty(
            scaling_type="TARGET_TRACKING_SCALING",
            max_capacity=scaling_config.max_capacity,
            **optional_props,
        )

        fleet_cn.scaling_configuration = scaling_configuration_input
            
    def _apply_tags(self) -> None:
        """Apply tags to the fleet and related resources."""
        for key, value in self.fleet_config.tags.items():
            Tags.of(self).add(key, value)


class AwsLcCodeBuildFleets(Stack):
    """CDK Stack for managing multiple CodeBuild fleets with configurable compute types and scaling."""

    def __init__(
        self,
        scope: Construct,
        id: str,
        env: typing.Union[Environment, typing.Dict[str, typing.Any]],
        config_path: Optional[str] = None,
        **kwargs
    ) -> None:
        super().__init__(scope, id, env=env, **kwargs)
        
        # Load configuration
        self.config = self._load_configuration(config_path)
        
        # Validate all fleet configurations
        self._validate_configurations()
        
        # Create fleets
        self.fleets: Dict[str, CodeBuildFleet] = {}
        self._create_fleets()
    
    def _load_configuration(self, config_path: Optional[str]) -> FleetConfigurationFile:
        """Load fleet configuration from YAML file."""
        if config_path:
            config_file_path = pathlib.Path(config_path)
        else:
            config_file_path = FleetConfigLoader.get_default_config_path()
        
        try:
            return FleetConfigLoader.load_config(config_file_path)
        except Exception as e:
            raise ValueError(f"Failed to load fleet configuration: {e}")
    
    def _validate_configurations(self) -> None:
        """Validate all fleet configurations."""
        all_errors = []
        fleet_names = set()
        
        for fleet_config in self.config.fleets:
            # Check for duplicate fleet names
            if fleet_config.name in fleet_names:
                all_errors.append(f"Duplicate fleet name: {fleet_config.name}")
            fleet_names.add(fleet_config.name)
            
            # Validate individual fleet configuration
            errors = validate_fleet_config(fleet_config)
            all_errors.extend(errors)
        
        if all_errors:
            error_message = "Fleet configuration validation failed:\n" + "\n".join(all_errors)
            raise ValueError(error_message)
    
    def _create_fleets(self) -> None:
        """Create all CodeBuild fleets based on configuration."""
        for fleet_config in self.config.fleets:
            fleet_construct = CodeBuildFleet(
                self,
                f"aws-lc-fleet-{fleet_config.name}",
                fleet_config=fleet_config
            )
            
            self.fleets[fleet_config.name] = fleet_construct
    
    def get_fleet_arn(self, fleet_name: str) -> str:
        """Get the ARN of a specific fleet."""
        if fleet_name not in self.fleets:
            raise ValueError(f"Fleet '{fleet_name}' not found")
        return self.fleets[fleet_name].fleet.attr_arn
    
    def get_all_fleet_arns(self) -> Dict[str, str]:
        """Get ARNs of all fleets."""
        return {
            name: fleet.fleet.attr_arn 
            for name, fleet in self.fleets.items()
        }
