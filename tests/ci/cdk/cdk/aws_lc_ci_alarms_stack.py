# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import typing

import jsii
from aws_cdk import (
    Duration,
    Environment,
    Stack,
    aws_cloudwatch as cloudwatch,
)
from constructs import Construct

from util.metadata import AWS_LC_METRIC_NS, PROD_ACCOUNT

# Format of the CloudWatch alarm action that cuts a SIM-T ticket:
#   arn:aws:cloudwatch::cwa-internal:ticket:<Severity>:<Category>:<Type>:<Item>:<ResolverGroup>:<DedupString>
# Spaces in a field are encoded as '+'. While a ticket with the same dedup string is open, further
# ALARM transitions attach to that ticket instead of cutting a new one, and the alarm is placed on
# the ticket as a hold so that it cannot be resolved while the alarm is in ALARM. Already-open
# tickets therefore follow the dedup string, not the alarm name: keep the dedup strings stable.
TICKET_ACTION_ARN_PREFIX = "arn:aws:cloudwatch::cwa-internal:ticket"
TICKET_SEVERITY = 4
TICKET_CTI = ("AWS", "AWS-LC", "Build Issue")
TICKET_RESOLVER_GROUP = "AWS-LC"


@jsii.implements(cloudwatch.IAlarmAction)
class SimTicketAlarmAction:
    """Alarm action that cuts a SIM-T ticket to TICKET_RESOLVER_GROUP, deduplicated on dedup_string."""

    def __init__(self, dedup_string: str) -> None:
        fields = (TICKET_SEVERITY, *TICKET_CTI, TICKET_RESOLVER_GROUP, dedup_string)
        self.arn = ":".join([TICKET_ACTION_ARN_PREFIX] + [str(x).replace(" ", "+") for x in fields])

    def bind(self, scope: Construct, alarm: cloudwatch.IAlarm) -> cloudwatch.AlarmActionConfig:
        return cloudwatch.AlarmActionConfig(alarm_action_arn=self.arn)


INTEGRATION_OMNIBUS_ALARM_DESCRIPTION = """\
Nightly integration omnibus detected one or more integration test failures against tip-of-main, blocking AWS-LC contributor PRs and mandatory CI.

Workflow: https://github.com/aws/aws-lc/actions/workflows/integration_omnibus.yml?query=event%3Aschedule

Action required:
1. Open the most recent scheduled run of integration_omnibus.yml (link above).
2. Identify the failed jobs in the Annotations panel.
3. Check whether the autofix workflow (autofix_integration_failures.yml, triggered by the failed run) already produced a patch.
4. Update the affected patches under tests/ci/integration/<name>_patch/ (https://github.com/aws/aws-lc/blob/main/tests/ci/integration/README.md).
"""

BSD_CI_ALARM_DESCRIPTION = """\
Nightly BSD CI detected one or more FreeBSD, OpenBSD, or NetBSD test failures against tip-of-main. Only a subset of these lanes runs on PRs, so the failure may be invisible to contributors until it is fixed.

Workflow: https://github.com/aws/aws-lc/actions/workflows/bsd-ci.yml?query=event%3Aschedule

Action required:
1. Open the most recent scheduled run of bsd-ci.yml (link above).
2. Identify the failed jobs in the Annotations panel and the failing tests in their logs.
3. Fix the failing tests, or the lane configuration in .github/workflows/bsd-ci.yml and tests/ci/run_bsd_tests.sh.
"""


class AwsLcCiAlarmsStack(Stack):
    """Alarms on the failure metrics that the nightly GitHub Actions workflows publish to AWS_LC_METRIC_NS.

    Each nightly workflow ends with a report-failures job (see .github/actions/report-workflow-failures) that
    publishes the number of failed jobs in that run as one datapoint. An alarm fires when a day's datapoints
    sum to at least one failure and cuts a ticket; a missing datapoint is treated as not breaching, so a
    nightly that stops running altogether is currently silent.
    """

    def __init__(
        self,
        scope: Construct,
        id: str,
        env: typing.Union[Environment, typing.Dict[str, typing.Any]],
        **kwargs
    ) -> None:
        super().__init__(scope, id, env=env, **kwargs)

        # Only the production account may cut tickets: staging and dev deployments get the same alarms
        # without actions so that they never page the team.
        self.cut_tickets = env.account == PROD_ACCOUNT

        self.integration_omnibus_alarm = self.nightly_failure_alarm(
            "IntegrationOmnibusFailure",
            alarm_name="Downstream Integration Tests Failure",
            metric_name="IntegrationOmnibusFailure",
            description=INTEGRATION_OMNIBUS_ALARM_DESCRIPTION,
            dedup_string="AWSLC_IntegrationOmnibusFailure_PDX",
        )

        self.bsd_ci_alarm = self.nightly_failure_alarm(
            "BsdCiFailure",
            alarm_name="BSD CI Tests Failure",
            metric_name="BsdCiFailure",
            description=BSD_CI_ALARM_DESCRIPTION,
            dedup_string="AWSLC_BsdCiFailure_PDX",
        )

    def nightly_failure_alarm(self, id: str, *, alarm_name: str, metric_name: str, description: str,
                              dedup_string: str) -> cloudwatch.Alarm:
        alarm = cloudwatch.Alarm(
            self, id,
            alarm_name=alarm_name,
            alarm_description=description,
            metric=cloudwatch.Metric(
                namespace=AWS_LC_METRIC_NS,
                metric_name=metric_name,
                statistic=cloudwatch.Stats.SUM,
                period=Duration.days(1),
            ),
            comparison_operator=cloudwatch.ComparisonOperator.GREATER_THAN_OR_EQUAL_TO_THRESHOLD,
            threshold=1,
            evaluation_periods=1,
            datapoints_to_alarm=1,
            treat_missing_data=cloudwatch.TreatMissingData.NOT_BREACHING,
        )
        if self.cut_tickets:
            alarm.add_alarm_action(SimTicketAlarmAction(dedup_string))
        return alarm
