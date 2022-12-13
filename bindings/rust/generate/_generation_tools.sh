# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

function usage {
  echo
  echo "Usage: $(basename "${0}") [-d] [-b] [-u] [-m] [-s]"
  echo
}

function generation_options {
	while getopts "dbums" option; do
	  case ${option} in
	  d )
	    IGNORE_DIRTY=1
	    ;;
	  b )
	    IGNORE_BRANCH=1
	    ;;
	  u )
	    IGNORE_UPSTREAM=1
	    ;;
	  m )
	    IGNORE_MACOS=1
	    ;;
	  s )
	    SKIP_TEST=1
	    ;;
	  * )
	    echo Invalid argument: -"${?}"
	    usage
	    exit 1
	    ;;
	  esac
	done
}

function check_workspace {
  if [[ $(git status --porcelain | wc -l) -gt 0 ]]; then
	echo Workspace is dirty.
	if [[ ${IGNORE_DIRTY} -eq 0 ]]; then
	  echo Aborting. Use '-d' to ignore.
	  echo
	  exit 1
	else
	  echo Ignoring dirty workspace.
	  echo
	fi
  fi
}

function check_branch {
  CURRENT_BRANCH=$(git rev-parse --abbrev-ref HEAD)
  if [ "${CURRENT_BRANCH}" != "main" ]
  then
    echo Branch is not main.
    if [[ ${IGNORE_BRANCH} -eq 0 ]]; then
      echo Aborting. Use '-b' to ignore.
      echo
      exit 1
    else
      echo Ignoring wrong branch.
      echo
    fi
  fi
  git fetch
  LOCAL_HASH=$(git rev-parse HEAD)
  UPSTREAM_HASH=$(git rev-parse "${CURRENT_BRANCH}"'@{upstream}')

  if [[ ! "${LOCAL_HASH}" == "${UPSTREAM_HASH}" ]]; then
    echo "${CURRENT_BRANCH}" not up to date with upstream.
    if [[ ${IGNORE_UPSTREAM} -eq 0 ]]; then
      echo Aborting. Use '-u' to ignore.
      echo
      exit 1
    else
      echo Ignoring branch not up to date.
      echo
    fi
  fi
}

function check_running_on_macos {
  if [[ ! "${OSTYPE}" == "darwin"* ]]; then
    echo This script is not running on MacOS.
    if [[ ${IGNORE_MACOS} -eq 0 ]]; then
      echo Aborting. Use '-m' to ignore.
      echo
      exit 1
    else
      echo Ignoring non-MacOS. Crate will not be tested and bindings will not be generated for Mac.
      echo
    fi
  fi
}

function create_symbol_file {
  if [[ ! -r "${SYMBOLS_FILE}" ]]; then
    echo Symbol file not found
    echo Performing build for supported platforms.
    source "${SCRIPT_DIR}"/_run_supported_symbol_builds.sh
  fi

  if [[ ! -r "${SYMBOLS_FILE}" ]]; then
    echo Symbol file not found after builds performed.
    exit 1
  else
    echo Symbol file generation complete
  fi
}

function create_prefix_headers {
  if [[ ! -r "${PREFIX_HEADERS_FILE}" || "${SYMBOLS_FILE}" -nt "${PREFIX_HEADERS_FILE}" ]]; then
    echo Prefix headers not up to date
    create_symbol_file

    echo Generating prefix headers
    go run "${AWS_LC_DIR}"/util/make_prefix_headers.go -out "${CRATE_AWS_LC_DIR}"/include "${SYMBOLS_FILE}"
  fi

  if [[ ! -r "${PREFIX_HEADERS_FILE}" || "${SYMBOLS_FILE}" -nt "${PREFIX_HEADERS_FILE}" ]]; then
    echo Prefix headers not up to date after generation.
    exit 1
  else
    echo Prefix headers generation complete
  fi
}
