# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

import os
import pathlib
import typing
from dataclasses import dataclass
from typing import Dict, List, Optional, Union

import yaml


@dataclass
class ScalingConfiguration:
    """Configuration for fleet auto-scaling."""
    enabled: bool = False
    utilization_rate: Optional[int] = None
    max_capacity: Optional[int] = None


@dataclass
class AttributeBasedCompute:
    """Configuration for attribute-based compute specifications."""
    vcpus: int
    memory: int  # in MB
    storage: int  # in GB


@dataclass
class FleetConfiguration:
    """Configuration for a single CodeBuild fleet."""
    name: str
    base_capacity: int
    environment_type: str
    scaling_configuration: ScalingConfiguration
    tags: Dict[str, str]
    
    # Compute type options (mutually exclusive)
    compute_type: Optional[str] = None
    custom_instance_type: Optional[str] = None
    attribute_based_compute: Optional[AttributeBasedCompute] = None
    
    def __post_init__(self):
        """Validate that exactly one compute type is specified."""
        compute_options = [
            self.compute_type,
            self.custom_instance_type,
            self.attribute_based_compute
        ]
        specified_options = [opt for opt in compute_options if opt is not None]
        
        if len(specified_options) != 1:
            raise ValueError(
                f"Fleet '{self.name}' must specify exactly one compute type: "
                f"computeType, customInstanceType, or attributeBasedCompute"
            )


@dataclass
class GlobalSettings:
    """Global configuration settings for all fleets."""
    default_tags: Dict[str, str]


@dataclass
class FleetConfigurationFile:
    """Complete configuration file structure."""
    fleets: List[FleetConfiguration]
    global_settings: GlobalSettings


class FleetConfigLoader:
    """Utility class to load and validate fleet configurations from YAML."""
    
    @staticmethod
    def load_config(config_path: Union[str, pathlib.Path]) -> FleetConfigurationFile:
        """
        Load fleet configuration from YAML file.
        
        Args:
            config_path: Path to the YAML configuration file
            
        Returns:
            FleetConfigurationFile: Parsed and validated configuration
            
        Raises:
            FileNotFoundError: If config file doesn't exist
            yaml.YAMLError: If YAML parsing fails
            ValueError: If configuration validation fails
        """
        config_path = pathlib.Path(config_path)
        
        if not config_path.exists():
            raise FileNotFoundError(f"Configuration file not found: {config_path}")
        
        with open(config_path, 'r') as file:
            raw_config = yaml.safe_load(file)
        
        return FleetConfigLoader._parse_config(raw_config)
    
    @staticmethod
    def _parse_config(raw_config: Dict) -> FleetConfigurationFile:
        """Parse raw YAML configuration into structured objects."""
        # Parse global settings
        global_settings_raw = raw_config.get('globalSettings', {})
        global_settings = GlobalSettings(
            default_tags=global_settings_raw.get('defaultTags', {})
        )
        
        # Parse fleet configurations
        fleets = []
        for fleet_raw in raw_config.get('fleets', []):
            fleet = FleetConfigLoader._parse_fleet(fleet_raw, global_settings)
            fleets.append(fleet)
        
        return FleetConfigurationFile(
            fleets=fleets,
            global_settings=global_settings
        )
    
    @staticmethod
    def _parse_fleet(fleet_raw: Dict, global_settings: GlobalSettings) -> FleetConfiguration:
        """Parse a single fleet configuration."""
        # Parse scaling configuration
        scaling_raw = fleet_raw.get('scalingConfiguration', {})
        scaling_config = ScalingConfiguration(
            enabled=scaling_raw.get('enabled', False),
            utilization_rate=scaling_raw.get('utilizationRate'),
            max_capacity=scaling_raw.get('maxCapacity', None),
        )
        
        # Parse attribute-based compute if present
        attribute_compute = None
        if 'attributeBasedCompute' in fleet_raw:
            attr_raw = fleet_raw['attributeBasedCompute']
            attribute_compute = AttributeBasedCompute(
                vcpus=attr_raw['vcpus'],
                memory=attr_raw['memory'],
                storage=attr_raw['storage']
            )
        
        # Merge tags with global defaults
        fleet_tags = fleet_raw.get('tags', {})
        merged_tags = {**global_settings.default_tags, **fleet_tags}
        
        return FleetConfiguration(
            name=fleet_raw['name'],
            base_capacity=fleet_raw['baseCapacity'],
            environment_type=fleet_raw['environmentType'],
            scaling_configuration=scaling_config,
            tags=merged_tags,
            compute_type=fleet_raw.get('computeType'),
            custom_instance_type=fleet_raw.get('customInstanceType'),
            attribute_based_compute=attribute_compute
        )
    
    @staticmethod
    def get_default_config_path() -> pathlib.Path:
        """Get the default path to the fleet configuration file."""
        # Assume we're running from the CDK directory
        current_dir = pathlib.Path(__file__).parent.parent
        return current_dir / 'config' / 'codebuild-fleets.yaml'


def validate_fleet_config(config: FleetConfiguration) -> List[str]:
    """
    Validate a fleet configuration and return list of validation errors.
    
    Args:
        config: Fleet configuration to validate
        
    Returns:
        List of validation error messages (empty if valid)
    """
    errors = []
    
    # Validate capacity values
    if config.base_capacity < 0:
        errors.append(f"Base capacity must be >= 0 for fleet '{config.name}'")
    
    # Validate scaling configuration
    scaling = config.scaling_configuration
    if scaling.enabled:
        if scaling.utilization_rate is not None and (scaling.utilization_rate < 0 or scaling.utilization_rate > 100):
            errors.append(
                f"Utilization rate ({scaling.utilization_rate}) must be >= 0 and <= 100"
                f"for fleet '{config.name}'"
            )

    # Validate attribute-based compute
    if config.attribute_based_compute:
        attr = config.attribute_based_compute
        if attr.vcpus <= 0:
            errors.append(f"vCPUs must be > 0 for fleet '{config.name}'")
        if attr.memory <= 0:
            errors.append(f"Memory must be > 0 for fleet '{config.name}'")
        if attr.storage <= 0:
            errors.append(f"Storage must be > 0 for fleet '{config.name}'")
    
    return errors
