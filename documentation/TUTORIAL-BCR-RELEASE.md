# Automated TRLC to BCR Release

This document describes the automated release flow that publishes TRLC
to the [Bazel Central Registry](https://github.com/bazelbuild/bazel-central-registry)
(BCR).

## How It Works

Releases are automated through GitHub Actions:

1. Push a release tag using the format `trlc-X.Y.Z`.
2. Workflow [`release.yml`](../.github/workflows/release.yml) creates a draft GitHub
   release and uploads `trlc-{TAG}.tar.gz`.
3. Workflow [`publish.yml`](../.github/workflows/publish.yml) opens a Bazel Central
   Registry PR through
   [publish-to-bcr](https://github.com/bazel-contrib/publish-to-bcr).
4. After BCR publish succeeds, the release is finalized (published),
   which triggers [`package.yml`](../.github/workflows/package.yml) to publish wheels to
   PyPI.

## Required Repository Secret

* `BCR_PUBLISH_TOKEN`: Classic PAT with `workflow` and `repo` scopes,
  with access to your BCR fork (default fork:
  `bmw-software-engineering/bazel-central-registry`).

## BCR Template Files

The [`.bcr/`](../.bcr/) directory contains template files used by the
`publish-to-bcr` action:

| File | Purpose |
|------|---------|
| [`presubmit.yml`](../.bcr/presubmit.yml) | Defines BCR presubmit CI: platforms, build/test targets |
| [`source.template.json`](../.bcr/source.template.json) | Template for the source archive URL and integrity hash |
| [`metadata.template.json`](../.bcr/metadata.template.json) | Module metadata (maintainers, homepage) |

## Presubmit Platforms

The BCR CI runs on platforms from the
[Bazel CI infrastructure](https://github.com/bazelbuild/continuous-integration/blob/master/buildkite/bazelci.py).
Currently configured: `ubuntu2204`, `windows`.

## Release Preparation Script

[`release_prep.sh`](../.github/workflows/release_prep.sh) is a helper that:

1. Validates the tag format (`trlc-X.Y.Z`)
2. Creates a reproducible source archive via `git archive`
3. Computes the SHA-256 checksum
4. Prints Markdown install snippets (Bzlmod and WORKSPACE) for release
   notes

## Triggering a Release

```bash
# Tag and push
git tag trlc-1.2.3
git push origin trlc-1.2.3
```

The `push: tags: ["trlc-*"]` trigger in [`release.yml`](../.github/workflows/release.yml) starts the
pipeline automatically.

## Manual Dispatch

Both [`release.yml`](../.github/workflows/release.yml) and [`publish.yml`](../.github/workflows/publish.yml) support `workflow_dispatch` for
manual re-runs from the GitHub Actions UI. You must provide:

* `tag_name`: the git tag (e.g. `trlc-1.2.3`)
* `registry_fork`: the BCR fork to push to (e.g.
  `bmw-software-engineering/bazel-central-registry`)
