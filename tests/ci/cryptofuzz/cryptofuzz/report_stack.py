from aws_cdk import core, \
    aws_s3 as s3, \
    aws_lambda as lambda_, \
    aws_s3_notifications as s3_notifications, \
    aws_iam as iam, \
    aws_secretsmanager as secretsmanager

from util.util import EnvUtil


# S3 Bucket creation for corpus, reports, interesting inputs, and lambda that creates the report
class ReportStack(core.Stack):

    def __init__(self, scope: core.Construct, id: str, commit_secret: secretsmanager.Secret, **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Fetch environment variables.
        corpus_bucket = EnvUtil.get("CORPUS_BUCKET", "cryptofuzz-corpus-bucket")
        report_bucket = EnvUtil.get("REPORT_BUCKET", "cryptofuzz-report-bucket")
        interesting_input_bucket = EnvUtil.get("INTERESTING_INPUT_BUCKET", "cryptofuzz-interesting-input-bucket")
        commit_secret_name = EnvUtil.get("COMMIT_SECRET_NAME", "CommitID")
        ubuntu_x86 = EnvUtil.get("UBUNTU_X86", "aws-lc-cryptofuzz-ubuntu-19-10--x86--clang-9x-sanitizer")
        fedora_x86 = EnvUtil.get("FEDORA_X86", "aws-lc-cryptofuzz-ubuntu-19-10--x86--clang-9x-sanitizer")
        ubuntu_aarch = EnvUtil.get("UBUNTU_AARCH", "aws-lc-cryptofuzz-ubuntu-19-10--x86--clang-9x-sanitizer")
        aws_account = EnvUtil.get("CDK_DEPLOY_ACCOUNT", "923900853817")

        # Create the S3 bucket for the corpus
        s3_corpus_bucket = s3.Bucket(self, corpus_bucket,
                                     bucket_name=corpus_bucket)

        # Create the S3 bucket for the reports
        s3_report_bucket = s3.Bucket(self, report_bucket,
                                     bucket_name=report_bucket)

        # Create the S3 bucket for the interesting inputs
        s3_interesting_input_bucket = s3.Bucket(self, interesting_input_bucket,
                                                bucket_name=interesting_input_bucket)

        # Create lambda that generates the reports after fuzzing is complete
        report_lambda = lambda_.Function(self, "report-lambda",
                                         runtime=lambda_.Runtime.PYTHON_3_7,
                                         code=lambda_.Code.from_asset("reportFunction"),
                                         handler="lambda_function.lambda_handler",
                                         environment={
                                             "REPORT_BUCKET": report_bucket,
                                             "CORPUS_BUCKET": corpus_bucket,
                                             "INTERESTING_INPUT_BUCKET": interesting_input_bucket,
                                             "COMMIT_SECRET_NAME": commit_secret_name,
                                             "UBUNTU_X86": ubuntu_x86,
                                             "FEDORA_X86": fedora_x86,
                                             "UBUNTU_AARCH": ubuntu_aarch
                                         },
                                         timeout=core.Duration.minutes(5))

        # Add event notification so that S3 bucket can trigger report lambda when interesting inputs are updated
        s3_interesting_input_bucket.add_event_notification(s3.EventType.OBJECT_CREATED,
                                                           s3_notifications.LambdaDestination(report_lambda),
                                                           s3.NotificationKeyFilter(
                                                               prefix='*'
                                                           ))

        # Granting S3 permissions to the report lambda
        s3_report_bucket.grant_read_write(report_lambda)
        s3_corpus_bucket.grant_read_write(report_lambda)
        s3_interesting_input_bucket.grant_read_write(report_lambda)
        commit_secret.grant_read(report_lambda)

        # Add S3 buckets trigger permissions to the report lambda resource policy
        report_lambda.add_permission(id="S3 Invoke Access",
                                     principal=iam.ServicePrincipal("s3.amazonaws.com"),
                                     source_arn=s3_interesting_input_bucket.bucket_arn,
                                     source_account=aws_account)
