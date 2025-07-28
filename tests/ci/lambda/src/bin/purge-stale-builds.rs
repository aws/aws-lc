use aws_config::BehaviorVersion;
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

use aws_sdk_codebuild::types::BuildBatchFilter;
use aws_sdk_ec2::operation::describe_instances::DescribeInstancesOutput;
use aws_sdk_ec2::primitives::DateTime;
use aws_sdk_ec2::types::Filter;
use aws_sdk_ssm::types::DocumentKeyValuesFilter;
use lambda_runtime::{service_fn, Error, LambdaEvent};
use serde_json::{json, Value};

#[tokio::main]
async fn main() -> Result<(), Error> {
    env_logger::init();
    let func = service_fn(handle);
    Box::pin(lambda_runtime::run(func)).await?;
    Ok(())
}

#[allow(clippy::too_many_lines)]
async fn handle(_event: LambdaEvent<Value>) -> Result<(), Error> {
    let region_provider =
        aws_config::meta::region::RegionProviderChain::default_provider().or_else("us-west-2");

    let config = aws_config::defaults(BehaviorVersion::latest())
        .region(region_provider)
        .load()
        .await;

    let sm_client = aws_sdk_secretsmanager::Client::new(&config);

    let github_token = retrieve_secret(
        &sm_client,
        std::env::var("GITHUB_TOKEN_SECRET_NAME")
            .map_err(|_| "failed to find github access token secret name")?,
    )
    .await?;

    let github = octocrab::initialise(octocrab::Octocrab::builder().personal_token(github_token))
        .map_err(|e| format!("failed to build github client: {e}"))?;

    let codebuild_client = aws_sdk_codebuild::Client::new(&config);

    let project = std::env::var("CODEBUILD_PROJECT_NAME").unwrap();

    let is_ec2_test_framework: bool = project == "aws-lc-ci-ec2-test-framework";

    let github_repo_owner = std::env::var("GITHUB_REPO_OWNER").unwrap();

    let mut pull_requests: HashMap<u64, Vec<CommitBuild>> = HashMap::new();

    log::info!("Pulling builds for {project}");

    let builds = get_project_build_batches(&codebuild_client, project.clone()).await?;

    let project_pull_requests = gather_pull_request_builds(&codebuild_client, builds).await?;

    for (k, v) in project_pull_requests {
        let mut builds = v;
        pull_requests
            .entry(k)
            .and_modify(|ev| {
                ev.append(&mut builds);
                ev.dedup();
            })
            .or_insert(builds);
    }

    let ec2_client_optional: Option<aws_sdk_ec2::Client> = if is_ec2_test_framework {
        Some(aws_sdk_ec2::Client::new(&config))
    } else {
        None
    };
    let ssm_client_optional: Option<aws_sdk_ssm::Client> = if is_ec2_test_framework {
        Some(aws_sdk_ssm::Client::new(&config))
    } else {
        None
    };

    // Filters for aws-lc-ec2-test-framework specific hosts.
    let ec2_framework_filters = vec![
        Filter::builder()
            .name("instance-state-name")
            .values("running")
            .build(),
        Filter::builder()
            .name("instance.group-name")
            .values("codebuild_ec2_sg")
            .build(),
        Filter::builder()
            .name("tag-key")
            .values("ec-framework-commit-tag")
            .build(),
    ];

    let ec2_describe_response_optional: Option<DescribeInstancesOutput> =
        if let Some(ref ec2_client) = ec2_client_optional {
            let result = ec2_client
                .describe_instances()
                .set_filters(Some(ec2_framework_filters))
                .send()
                .await;
            match result {
                Ok(output) => Some(output),
                Err(err) => {
                    eprintln!("EC2 Describe Instances Failed: {err:?}");
                    return Err(Error::from(err.to_string()));
                }
            }
        } else {
            None
        };

    let mut ssm_deleted_documents: Vec<String> = vec![];
    let mut ec2_terminated_instances: Vec<String> = vec![];
    let mut stopped_builds: u64 = 0;

    let now_as_secs = DateTime::from(SystemTime::now()).secs();
    // Instances do not properly shut down from time to time. Gather a list of all hanging ec2
    // instances longer than 2 hours that fall under that umbrella.
    if let Some(ref ec2_describe_response) = ec2_describe_response_optional {
        for reservation in ec2_describe_response.reservations() {
            for instance in reservation.instances() {
                let launch_elapsed_time = now_as_secs - instance.launch_time().unwrap().secs();
                if launch_elapsed_time > 7200 {
                    ec2_terminated_instances.push(instance.instance_id().unwrap().to_string());
                    log::info!("Instance {:?} will be terminated.", reservation.instances());
                }
            }
        }
    }
    log::info!("Instances {:?}", ec2_terminated_instances);

    for (k, v) in &pull_requests {
        if v.len() <= 1 {
            continue;
        }
        let pull = github
            .pulls(&github_repo_owner, "aws-lc")
            .get(*k)
            .await
            .map_err(|e| format!("failed to retrieve GitHub pull requests: {e:?}"))?;
        let commit: String = pull.head.sha;
        for cb in v {
            let build_id = cb.build();
            if cb.commit() == commit {
                log::info!("{build_id} pr/{k} at current head({commit})");
                continue;
            }
            let old_commit = cb.commit();

            // Prune unneeded codebuild batches.
            log::info!("{build_id} pr/{k} at old head({old_commit}) will be canceled");
            codebuild_client
                .stop_build_batch()
                .set_id(Some(String::from(build_id)))
                .send()
                .await
                .map_err(|e| format!("failed to stop_build_batch: {e}"))?;
            stopped_builds += 1;

            // Gather a list of all unneeded ec2 instances and terminate after the loop.
            if let Some(ref ec2_describe_response) = ec2_describe_response_optional {
                // Prune unneeded ec2 instances.
                for reservation in ec2_describe_response.reservations() {
                    log::info!("Checking Instance {:?}", reservation.instances());
                    for instance in reservation.instances() {
                        for tag in instance.tags() {
                            log::info!("Tag: {:?}", tag);
                            if tag.key().unwrap() == "ec-framework-commit-tag"
                                && tag.value().unwrap() == old_commit
                            {
                                ec2_terminated_instances
                                    .push(instance.instance_id().unwrap().to_string());
                            }
                        }
                    }
                }
            }

            // Gather a list of old commits. The SSM documents should have the commits within
            // their document name.
            ssm_deleted_documents.push(old_commit.to_string());
        }
    }

    log::info!("Terminating instances {:?}", ec2_terminated_instances);
    if let Some(ref ec2_client) = ec2_client_optional {
        if !ec2_terminated_instances.is_empty() {
            ec2_client
                .terminate_instances()
                .set_instance_ids(Some(ec2_terminated_instances.clone()))
                .send()
                .await
                .map_err(|e| format!("failed to terminate hanging instances: {e}"))?;
        }
    }

    if !ssm_deleted_documents.is_empty() && is_ec2_test_framework {
        log::info!(
            "Query for list of documents to delete with: {:?}",
            ssm_deleted_documents
        );

        let all_documents =
            get_ssm_document_list(&ssm_client_optional, ssm_deleted_documents.clone()).await?;

        // Prune hanging ssm documents corresponding to commits.
        for document in all_documents {
            log::info!("SSM document {:?} will be deleted", document);
            if let Some(ref ssm_client) = ssm_client_optional {
                ssm_client
                    .delete_document()
                    .name(document)
                    .send()
                    .await
                    .map_err(|e| format!("failed to delete ssm document: {e}"))?;
            }
        }
    }

    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis();

    println!(
        "{}",
        json!({
            "_aws": {
                "CloudWatchMetrics": [{
                    "Namespace": "AWS-LC",
                    "Dimensions": [
                        ["Project"]
                    ],
                    "Metrics": [
                        {
                            "Name": "PrunedGitHubBuilds",
                            "Unit": "Count",
                            "StorageResolution": 60
                        },
                        {
                            "Name": "TerminatedEC2Instances",
                            "Unit": "Count",
                            "StorageResolution": 60
                        }
                    ]
                }],
                "Timestamp": timestamp
            },
            "Project": &project,
            "PrunedGitHubBuilds": stopped_builds,
            "TerminatedEC2Instances": ec2_terminated_instances.len()
        })
    );

    Ok(())
}

async fn retrieve_secret(
    client: &aws_sdk_secretsmanager::Client,
    secret_id: String,
) -> Result<String, String> {
    let github_secret_output = client
        .get_secret_value()
        .set_secret_id(Some(secret_id))
        .send()
        .await
        .map_err(|e| format!("failed to retrieve GitHub secret: {e}"))?;

    if github_secret_output.secret_string().is_none() {
        return Err("retrieved secret did not have content".to_string());
    }

    Ok(String::from(github_secret_output.secret_string().unwrap()))
}

#[derive(PartialEq, Eq)]
struct CommitBuild(String, String);

impl CommitBuild {
    fn new(commit: String, build: String) -> Self {
        Self(commit, build)
    }

    fn commit(&self) -> &str {
        self.0.as_str()
    }

    fn build(&self) -> &str {
        self.1.as_str()
    }
}

async fn gather_pull_request_builds(
    client: &aws_sdk_codebuild::Client,
    builds: Vec<String>,
) -> Result<HashMap<u64, Vec<CommitBuild>>, String> {
    let mut pull_requests: HashMap<u64, Vec<CommitBuild>> = HashMap::new();

    for chunk in builds.chunks(100) {
        if chunk.is_empty() {
            break;
        }

        let batch = client
            .batch_get_build_batches()
            .set_ids(Some(Vec::from(chunk)))
            .send()
            .await;
        if batch.is_err() {
            return Err(format!(
                "failed to get batch details: {}",
                batch.unwrap_err()
            ));
        }

        for bb in batch.unwrap().build_batches() {
            if bb.source().is_none() {
                continue;
            }
            let source = bb.source().unwrap();
            if source.r#type().as_str() != aws_sdk_codebuild::types::SourceType::Github.as_str()
                || bb.source_version().is_none()
                || bb.resolved_source_version().is_none()
            {
                continue;
            }

            let source_version = bb.source_version().unwrap_or("");

            if !source_version.contains("pr/") {
                continue;
            }

            let pr_number = String::from(source_version).replace("pr/", "");
            let commit = String::from(bb.resolved_source_version().unwrap_or_default());
            let build_id = String::from(bb.id().unwrap_or_default());

            if pr_number.is_empty() || commit.is_empty() || build_id.is_empty() {
                continue;
            }

            pull_requests
                .entry(pr_number.parse::<u64>().unwrap())
                .and_modify(|e| e.push(CommitBuild::new(commit.clone(), build_id.clone())))
                .or_insert(vec![CommitBuild::new(commit, build_id)]);
        }
    }

    for v in &mut pull_requests.values_mut() {
        v.dedup();
    }

    Ok(pull_requests)
}

async fn get_project_build_batches(
    client: &aws_sdk_codebuild::Client,
    project: String,
) -> Result<Vec<String>, String> {
    let mut builds: Vec<String> = vec![];

    let mut paginator = client
        .list_build_batches_for_project()
        .set_project_name(Some(project))
        .set_filter(Some(
            BuildBatchFilter::builder()
                .set_status(Some(aws_sdk_codebuild::types::StatusType::InProgress))
                .build(),
        ))
        .into_paginator()
        .send();

    while let Some(result) = paginator.next().await {
        if result.is_err() {
            return Err(format!(
                "failed to list_build_batches_for_project: {}",
                result.unwrap_err()
            ));
        }

        let mut ids = Vec::from(result.unwrap().ids());

        builds.append(&mut ids);
    }

    Ok(builds)
}

async fn get_ssm_document_list(
    client: &Option<aws_sdk_ssm::Client>,
    ssm_deleted_documents: Vec<String>,
) -> Result<Vec<String>, String> {
    let ssm_client_filters = vec![
        DocumentKeyValuesFilter::builder()
            .key("SearchKeyword")
            .set_values(Some(ssm_deleted_documents))
            .build(),
        DocumentKeyValuesFilter::builder()
            .key("Owner")
            .values("Self")
            .build(),
    ];
    log::info!("Document filter list: {:?}", ssm_client_filters);

    let mut document_list: Vec<String> = vec![];

    if let Some(ref ssm_client) = client {
        let mut paginator = ssm_client
            .list_documents()
            .set_filters(Some(ssm_client_filters))
            .into_paginator()
            .send();

        while let Some(result) = paginator.next().await {
            if result.is_err() {
                return Err(format!("SSM ListDocuments Failed: {}", result.unwrap_err()));
            }

            let document_ids = Vec::from(result.unwrap().document_identifiers());

            for document in document_ids {
                document_list.push(document.name.unwrap())
            }
        }
    }

    log::info!("Found documents to delete {:?}", document_list);

    Ok(document_list)
}
