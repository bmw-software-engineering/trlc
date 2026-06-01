#!/usr/bin/env bash

set -o errexit -o nounset -o pipefail

TAG="$1"
# Tags use the format "trlc-X.Y.Z"; strip the prefix to get the bare version
# matching the tag_prefix configured in publish.yml
if [[ "$TAG" == trlc-* ]]; then
  VERSION="${TAG#trlc-}"
else
  echo "ERROR: tag '${TAG}' does not match expected format 'trlc-X.Y.Z'" >&2
  exit 1
fi

mkdir -p archives

PREFIX="trlc-${VERSION}"
ARCHIVE="archives/${TAG}.tar.gz"

git archive --format=tar --prefix="${PREFIX}/" "$TAG" | gzip > "$ARCHIVE"

SHA=$(sha256sum "$ARCHIVE" | awk '{print $1}')

cat << EOF
## Bzlmod

Add this to your MODULE.bazel:

\`\`\`starlark
bazel_dep(name = "trlc", version = "${VERSION}")
\`\`\`

## WORKSPACE

\`\`\`starlark
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
http_archive(
    name = "trlc",
    sha256 = "${SHA}",
    strip_prefix = "${PREFIX}",
    url = "https://github.com/bmw-software-engineering/trlc/releases/download/${TAG}/${TAG}.tar.gz",
)
\`\`\`
EOF
