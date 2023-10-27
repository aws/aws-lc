# Integration CI for AWS-LC
We're adding backend support for more open source projects. This folder contains integration scripts and patches to test within our CI, until we add official support within these projects.

## Updating a failed patch
Most of these integration scripts pin to the main branch. This causes some expected churn in the patches when relevant code within the projects are updated. To update an outdated patch, follow the steps below:

1. Run the corresponding test script that's failing to patch. (e.g. `./tests/ci/integration/run_nginx_integration.sh`)
2. `cd` into the `SCRATCH_FOLDER` defined by the script. This will be in the same or one level above your local aws-lc directory.
3. Check out the patch that was failing and fix it. Once the conflicts are resolved, run `git diff > temp.patch` to save your new patch.
4. Move your patch to the patch directory the test script is using (e.g. `mv temp.patch ../../aws-lc/tests/ci/integration/nginx_patch/temp.patch`. Remember to remove the original failing patch, so the script doesn't fail again.
5. Rerun the integration test script. If the build and tests pass, rename the new integration patch to something more suitable and ship it.

