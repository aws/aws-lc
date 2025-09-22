#!/usr/bin/env bash

set -ex

# Function to parse INPUT_ENV and convert to -e flags
parse_env_vars() {
    local env_string="$1"
    local env_flags=""
    
    # Return empty if INPUT_ENV is not set or empty
    if [[ -z "$env_string" ]]; then
        echo ""
        return
    fi
    
    # Process each line as a single key=value pair or just key
    while IFS= read -r line; do
        # Skip empty lines
        [[ -z "$line" ]] && continue
        
        # Check if line contains an equals sign
        if [[ "$line" == *"="* ]]; then
            # Extract key and value
            key="${line%%=*}"
            value="${line#*=}"
            
            # Skip if key is empty
            [[ -z "$key" ]] && continue
            
            # Add -e flag with proper quoting
            env_flags="$env_flags -e $key=\"$value\""
        else
            # Line is just a key name, pass current environment value
            key="$line"
            
            # Skip if key is empty
            [[ -z "$key" ]] && continue
            
            # Add -e flag without value (Docker will use current environment)
            env_flags="$env_flags -e $key"
        fi
    done <<< "$env_string"
    
    echo "$env_flags"
}

# Parse environment variables from INPUT_ENV
ENV_FLAGS=$(parse_env_vars "$INPUT_ENV")

exec docker run -v /var/run/docker.sock:/var/run/docker.sock \
    -v ${GITHUB_WORKSPACE}:${GITHUB_WORKSPACE} \
    -w ${GITHUB_WORKSPACE} \
    ${INPUT_OPTIONS:-} \
    -e GOPROXY \
    ${ENV_FLAGS} \
    --entrypoint=${INPUT_SHELL} ${INPUT_IMAGE} \
    -c "${INPUT_RUN//$'\n'/;}"
