## Building Windows Docker Images and Uploading them to AWS Elastic Container Service
### Prerequisites
* An host to build the image with
  * Windows Server 2019 with Containers. The EC2 AMI
    EC2LaunchV2-Windows_Server-2019-English-Full-ContainersLatest-2021.12.15 was used to build the
    images used by this repository
* Docker
  * To install run the following in an admin powershell of your new instance:
    ```
    Install-Module DockerMsftProvider -Force
    Install-Package Docker -ProviderName DockerMsftProvider -Force
    (Install-WindowsFeature Containers).RestartNeeded
    Restart-Computer
    ```
   * See [docker docs](https://docs.docker.com/install/windows/docker-ee/) for
   latest instructions
* AWS CLI
  * Installed by default in EC2 AMI, used to push the docker images 

### Build the images
In a PowerShell prompt run:
```
build_images.ps1
```
You can test the images by running `docker run -it vs2015` or `docker run -it
vs2017`. To emulate a CodeBuild run locally execute the following inside one of
the docker images :
```
$ git clone https://github.com/aws/aws-lc.git -b main --depth 1
$ cd aws-lc
# Depending on the docker image run:
$ .\tests\ci\run_windows_tests.bat "C:\Program Files (x86)\Microsoft Visual Studio 14.0\VC\vcvarsall.bat" x64
# or
$ .\tests\ci\run_windows_tests.bat "C:\Program Files (x86)\Microsoft Visual Studio 15.0\VC\vcvarsall.bat" x64
```

### Push the images
If you are publishing to your own account, update the `ECS_REPO` value in
`push_images.ps1`. You can find the correct URI in the AWS Console for your ECR
repository.

Once you have `ECS_REPO` set properly, and you have configured your Powershell
AWS CLI credentials correctly, simply _source_ push_images.ps1 `. .\push.ps1`.

Note that because powershell CLI credentials are per-powershell-session, it's
important to use dot-sourcing if you use the `Set-AWSCredential` cmdlet to
configure your credentials. If you're using EC2 Instance Roles, then it's not
strictly necessary to dot-source the script.