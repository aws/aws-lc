#!/usr/bin/env python3

import os
import subprocess
import json
import re
from typing import List, Tuple
from pathlib import Path

REMOTE_NAME = "origin"
TAG_BRANCH_JSON = Path(__file__).parent / 'tag-branch.json'
REPO_PATH = Path(__file__).parent.parent


class GitError(Exception):
    pass


def run_git_command(args: List[str], error_msg: str) -> subprocess.CompletedProcess:
    try:
        return subprocess.run(
            args,
            capture_output=True,
            text=True,
            check=True
        )
    except subprocess.CalledProcessError as e:
        raise GitError(f"{error_msg}: {e.stderr.strip()}")


def get_git_tags() -> List[str]:
    result = run_git_command(
        ['git', '-C', str(REPO_PATH), 'tag', '--list'],
        "Error getting tags"
    )
    return [tag for tag in result.stdout.strip().split('\n') if tag]


def get_commit_sha(ref: str) -> str:
    result = run_git_command(
        ['git', '-C', str(REPO_PATH), 'rev-parse', ref],
        f"Error getting SHA for {ref}"
    )
    return result.stdout.strip()


def verify_ref_exists(ref: str) -> None:
    run_git_command(
        ['git', '-C', str(REPO_PATH), 'rev-parse', '--verify', ref],
        f"Reference {ref} does not exist"
    )


def is_tag_reachable(tag: str, branch: str) -> bool:
    # Verify both references exist
    verify_ref_exists(tag)
    verify_ref_exists(branch)

    tag_sha = get_commit_sha(tag)
    branch_sha = get_commit_sha(branch)
    if tag_sha != branch_sha:
        # An exception will occur if the return code != 0
        run_git_command(
            ['git', '-C', str(REPO_PATH), 'merge-base', '--is-ancestor', tag, branch],
            f"Error checking if {tag} is ancestor of {branch}"
        )

    return True



def load_branch_tag_patterns() -> List[dict]:
    try:
        with open(TAG_BRANCH_JSON) as file:
            patterns = json.load(file)
            if not patterns:
                raise Exception("Empty JSON file")
            return patterns
    except json.JSONDecodeError as e:
        raise Exception(f"Invalid JSON file: {e}")
    except IOError as e:
        raise Exception(f"Error reading JSON file: {e}")


def main():
    try:
        branch_tag_patterns = load_branch_tag_patterns()

        run_git_command(
            ['git', '-C', str(REPO_PATH), 'fetch', '--tags', REMOTE_NAME],
            "Error fetching tags"
        )

        # Get tags
        tags = get_git_tags()
        if not tags:
            raise GitError("No tags found")

        # Process patterns
        for item in branch_tag_patterns:
            branch = item['branch']
            tag_pattern = item['tag_pattern']
            print(f"Processing branch: '{branch}', pattern: '{tag_pattern}'")

            for tag in tags:
                if re.match(tag_pattern, tag):
                    full_branch = f"{REMOTE_NAME}/{branch}"
                    if is_tag_reachable(tag, full_branch):
                        print(f"Tag found: {tag} on branch: {branch}")
                    else:
                        raise GitError(f"Tag NOT found: {tag} on branch: {branch}")

    except GitError as e:
        print(f"Error: {e}")
        exit(1)


if __name__ == '__main__':
    main()
