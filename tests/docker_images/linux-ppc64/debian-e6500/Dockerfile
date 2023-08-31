# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM debian-ppc64:test

SHELL ["/bin/bash", "-c"]

COPY qemu-wrapper.sh /usr/bin/qemu-wrapper

CMD ["/bin/bash"]

ENTRYPOINT ["/usr/bin/qemu-wrapper"]
