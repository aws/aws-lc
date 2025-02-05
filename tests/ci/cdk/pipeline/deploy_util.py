from enum import Enum

class DeployEnvironmentType(Enum):
    PRE_PROD="Staging"
    PROD="Prod"
    DEV="Dev"