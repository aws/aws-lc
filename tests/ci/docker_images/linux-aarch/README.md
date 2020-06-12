# Prerequistes
EC2 ARM Ubuntu 19.10 host with Docker server installed (Docker instructions
taken from 
[Docker docs](https://docs.docker.com/install/linux/docker-ce/ubuntu/)):
```
$ sudo apt-get update
$ sudo apt-get install -y awscli apt-transport-https ca-certificates curl gnupg-agent software-properties-common
$ curl -fsSL https://download.docker.com/linux/ubuntu/gpg | sudo apt-key add -
$ sudo add-apt-repository "deb [arch=arm64] https://download.docker.com/linux/ubuntu $(lsb_release -cs) stable"
$ sudo apt-get update
$ sudo apt-get install -y docker-ce
$ sudo usermod -aG docker ${USER}
# Log in and out
```

Build images locally with `build_images.sh`, to push to the main repository run
`push_images.sh`. To push to your own repository pass in a complete ECS url
`push_images.sh ${ACCOUNT_ID}.dkr.ecr.${REGION}.amazonaws.com/${REPOSITORY}`. 
