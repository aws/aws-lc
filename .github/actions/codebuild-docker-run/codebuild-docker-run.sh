#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

# Function to parse INPUT_ENV and convert to -e flags
parse_env_vars() {
    local env_string="$1"
    local env_flags=""
    
    if [[ -z "$env_string" ]]; then
        echo ""
        return
    fi
    
    # Process each line as a single key=value pair or just key
    while IFS= read -r line; do
        [[ -z "$line" ]] && continue
        
        # Check if line contains an equals sign
        if [[ "$line" == *"="* ]]; then
            # Extract key and value
            key="${line%%=*}"
            value="${line#*=}"
            
            [[ -z "$key" ]] && continue
            
            # Add -e flag with proper quoting
            env_flags="$env_flags -e $key=\"$value\""
        else
            key="$line"
            
            [[ -z "$key" ]] && continue
            
            env_flags="$env_flags -e $key"
        fi
    done <<< "$env_string"
    
    echo "$env_flags"
}

# Parse environment variables from INPUT_ENV
ENV_FLAGS=$(parse_env_vars "$INPUT_ENV")

DOCKER_OPTIONS="${INPUT_OPTIONS:-}"
if [[ "${INPUT_IPV6}" == "true" && ! "${DOCKER_OPTIONS}" =~ --privileged ]]; then
    DOCKER_OPTIONS="$DOCKER_OPTIONS --privileged"
fi

PASSTHRU_ENV_VARS=("GOPROXY" "AWS_DEFAULT_REGION" "AWS_REGION")

if [[ "${INPUT_WITH_CREDENTIALS}" == true ]] &&
    [[ ! "${ENV_FLAGS}" =~ ECS_CONTAINER_METADATA_URI_V4 ]] && 
    [[ ! "${ENV_FLAGS}" =~ AWS_CONTAINER_CREDENTIALS_RELATIVE_URI ]]; then
    PASSTHRU_ENV_VARS+=(ECS_CONTAINER_METADATA_URI_V4 AWS_CONTAINER_CREDENTIALS_RELATIVE_URI)
fi

for ev in "${PASSTHRU_ENV_VARS[@]}"; do
    if [[ ! "${ENV_FLAGS}" =~ ${ev} ]]; then
        ENV_FLAGS="${ENV_FLAGS} -e ${ev}"
    fi
done

exec docker run -v /var/run/docker.sock:/var/run/docker.sock \
    -v ${GITHUB_WORKSPACE}:${GITHUB_WORKSPACE} \
    -w ${GITHUB_WORKSPACE} \
    ${DOCKER_OPTIONS} \
    ${ENV_FLAGS} \
    --entrypoint=${INPUT_SHELL} ${INPUT_IMAGE} \
    -c "cat > /tmp/actions-run.sh <<- 'EOF' && chmod +x /tmp/actions-run.sh && /tmp/actions-run.sh
    set -ex

    if [[ \"${INPUT_IPV6}\" == \"true\" ]]; then
        sysctl -w net.ipv6.conf.all.disable_ipv6=0
    fi

    if [[ \"${INPUT_USER}z\" != \"z\" ]]; then
        mkdir -p /home/${INPUT_USER}
        chown -R ${INPUT_USER}:${INPUT_USER} /home/${INPUT_USER}
        chown -R ${INPUT_USER}:${INPUT_USER} /codebuild/output
        export CONTAINER_PATH=\${PATH}
        cat > /tmp/run-as.sh <<- 'EOSU' && chmod +x /tmp/run-as.sh && su -p ${INPUT_USER} /tmp/run-as.sh
            set -ex
            export HOME=/home/${INPUT_USER}
            export PATH=\${CONTAINER_PATH}
            unset CONTAINER_PATH
            pushd ${GITHUB_WORKSPACE}
            ${INPUT_RUN}
            popd
EOSU
    else
        ${INPUT_RUN}
    fi
EOF
"
