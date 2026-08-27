#!/usr/bin/env bash
set -euo pipefail

# For `bazel run`, this points at the checkout root.
workspace_dir="${BUILD_WORKSPACE_DIRECTORY:-$PWD}"
cd "$workspace_dir"

rm -rf htmlcov
find . -name '.coverage*' -type f -delete
find . -name '*.pyc' -type f -delete

echo "All .coverage, .coverage.* and *.pyc files deleted."
