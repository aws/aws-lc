import os
import subprocess
import json
import re
from typing import List

REMOTE_NAME = "origin"
TAG_BRANCH_JSON = os.path.abspath(os.path.join(os.path.dirname(__file__), 'tag-branch.json'))
REPO_PATH = os.path.abspath(os.path.join(__file__, '..', '..'))


def get_git_tags(repo_path: str) -> List[str]:
    try:
        result = subprocess.run(
            ['git', '-C', repo_path, 'tag', '--list'],
            capture_output=True,
            text=True,
            check=True
        )

        tags = result.stdout.strip().split('\n')

        # Remove empty strings from list
        return [tag for tag in tags if tag]

    except subprocess.CalledProcessError as e:
        print(f"Error getting tags: {e}")
        return []

def is_same_commit(tag: str, branch: str) -> bool:
    tag_result = subprocess.run(
        ['git', '-C', REPO_PATH, 'rev-parse', tag],
        capture_output=True,
        text=True,
        check=True
    )
    tag_sha = tag_result.stdout.strip()

    branch_result = subprocess.run(
        ['git', '-C', REPO_PATH, 'rev-parse', branch],
        capture_output=True,
        text=True,
        check=True
    )
    branch_sha = branch_result.stdout.strip()

    #print(f"Comparing {tag_sha} and {branch_sha}")
    return tag_sha == branch_sha

def is_tag_reachable(tag: str, branch: str) -> bool:
    # Sanity check - Verify the tag exists
    subprocess.run(
        ['git', '-C', REPO_PATH, 'rev-parse', '--verify', tag],
        capture_output=True,
        check=True
    )

    # Sanity check - Verify the branch exists
    subprocess.run(
        ['git', '-C', REPO_PATH, 'rev-parse', '--verify', branch],
        capture_output=True,
        check=True
    )

    result = subprocess.run(
        ['git', '-C', REPO_PATH, 'merge-base', '--is-ancestor', tag, branch],
        capture_output=True,
        text=True
    )

    return result.returncode == 0 or is_same_commit(tag, branch)

def main():
    with open(TAG_BRANCH_JSON, 'r') as file:
        branch_tag_patterns = json.load(file)

    if len(branch_tag_patterns) == 0:
        raise Exception("Empty JSON file?")

    result = subprocess.run(
        ['git', '-C', REPO_PATH, 'fetch', '--tags', REMOTE_NAME],
        capture_output=True,
        text=True,
        check=True
    )
    if result.returncode != 0:
        raise Exception("Error fetching tags")

    tags = get_git_tags(REPO_PATH)
    if len(tags) == 0:
        raise Exception("No tags found")

    for item in branch_tag_patterns:
        branch = item['branch']
        tag_pattern = item['tag_pattern']
        print(f"Processing branch: '{branch}', pattern: '{tag_pattern}'")
        for tag in tags:
            if re.match(tag_pattern, tag):
                if is_tag_reachable(tag, '/'.join([REMOTE_NAME, branch])):
                    print(f"Tag found: {tag} on branch: {branch}")
                else:
                    raise Exception(f"Tag NOT found: {tag} on branch: {branch}")

if __name__ == '__main__':
    main()
