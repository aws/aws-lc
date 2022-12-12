# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

function publish_options {
	while getopts "d:sp" option; do
	  case ${option} in
	  d )
	    # For example:
	    # ./publish.sh -d 0.1.1
	    PREV_VERSION="$OPTARG"
	    ;;
	  # The public API diff should only be skipped if releasing a new major version
	  # (or a new minor version when the major version number is 0).
	  s )
	    SKIP_DIFF=1
	    ;;
	  p )
	    PUBLISH=1
	    ;;
	  * )
	    echo Invalid argument: -"${?}"
	    usage
	    exit 1
	    ;;
	  esac
	done
}

# Remove the internal_generation feature for bindings pre-generation before publishing.
function remove_internal_feature {
  if [[ "$(uname)" == "Darwin" ]]; then
    find ./ -type f  -name "Cargo.toml" | xargs sed -i '' -e "s|${INTERNAL_FEATURE_STRING}||g"
  else
    find ./ -type f  -name "Cargo.toml" | xargs sed -i -e "s|${INTERNAL_FEATURE_STRING}||g"
  fi
}

function find_completion_marker {
	local marker="$@"
	if [[ ! -f "${marker}" ]]; then
	  echo
	  echo The crate generation script must exit successfully before publishing.
	  echo
	  exit 1
	fi
}

function run_prepublish_checks {
	${SCRIPT_DIR}/_publish_checks.sh "$@"
}

# FIPS static build is only supported on linux.
function run_prepublish_checks_linux {
	docker run -v "${AWS_LC_DIR}":"${AWS_LC_DIR}" -w "${AWS_LC_DIR}" --rm --platform linux/amd64 rust:linux-x86_64 /bin/bash "${SCRIPT_DIR}"/_publish_checks.sh "$@"
}

function publish_crate {
	local crate="$@"
	if [[ "${SKIP_DIFF}" -eq 0 ]]; then
	  if [[ "${PREV_VERSION}" == "0" ]]; then
	    echo Aborting. Must specify previous crate version for API diff.
	    exit 1;
	  fi
	  cargo public-api --deny changed --deny removed --diff-published "${crate}@${PREV_VERSION}"
	fi
	cargo publish --dry-run --allow-dirty --no-verify

	if [[ ${PUBLISH} -eq 1 ]]; then
	  # The --no-verify is needed because we create `src/bindings.rs` during the build process.
	  # The maximum crate size allowed by crates-io is 10MB.
	  cargo publish --allow-dirty --no-verify
	else
	  echo Not published. Use -p to publish.
	fi
}