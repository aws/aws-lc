# Prerequistes

* [Create GitHub Personal Access Token](https://docs.github.com/en/github/authenticating-to-github/creating-a-personal-access-token)
  * Note: This token ONLY needs ['read:packages' permission](https://docs.github.com/en/packages/learn-github-packages/about-github-packages#authenticating-to-github-packages), and should be deleted from GitHub account after docker image build.
  * This token is needed when pulling images from 'docker.pkg.github.com'.

# Usage

## Docker image build and pull.
Build images locally with `build_images.sh`, which pulls Docker images from Docker hub.  
Pull images from 'docker.pkg.github.com' with `pull_github_pkg.sh`.

## Docker image push.
To push to the ECR repository of default AWS account, run `push_images.sh`.  
To push to the ECR repository pass in a complete ECS url `push_images.sh ${ACCOUNT_ID}.dkr.ecr.${REGION}.amazonaws.com/${REPOSITORY}`. 
