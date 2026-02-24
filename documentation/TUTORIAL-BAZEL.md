# Using TRLC with Bazel

TRLC ships Bazel macros in [`trlc.bzl`](@trlc//trlc.bzl)

## Setup

```python
# MODULE.bazel
bazel_dep(name = "trlc", version = "x.x.x")
```

```python
# BUILD
load("@trlc//:trlc.bzl",
     "trlc_specification",
     "trlc_requirements",
     "trlc_requirements_test",
     "trlc_specification_test")
```

It includes the pre-built CVC5 binary for Linux, macOS, and Windows.

---

## Public API

### `trlc_specification(name, srcs)`

Collects `.rsl` schema files into a bazel target.

| Attribute | Description |
|-----------|-------------|
| `name` | Target name. |
| `srcs` | `*.rsl` files. |

---

### `trlc_requirements(name, srcs, spec=[], deps=[])`

Collects `.trlc` requirement files, wired to their schema and any
imported packages.

| Attribute | Description |
|-----------|-------------|
| `name` | Target name. |
| `srcs` | `*.trlc` files. |
| `spec` | Direct `trlc_specification` targets. |
| `deps` | Other `trlc_requirements` targets whose packages are imported. |

---

### `trlc_requirements_test(name, reqs, srcs=…, main=…)`

Runs `trlc --verify`. The test passes when TRLC reports no errors.
Pass a custom `srcs`/`main` to run your own Python script instead
of the built-in CLI (see [TUTORIAL-API.md](TUTORIAL-API.md)).

| Attribute | Description |
|-----------|-------------|
| `name` | Target name. |
| `reqs` | `trlc_requirements` targets to validate. |
| `srcs` | Override the entry-point script (optional). |
| `main` | Filename of the entry point (required when `srcs` is set). |

---

### `trlc_specification_test(name, reqs)`

Like `trlc_requirements_test` but passes `--skip-trlc-files`. Use
this to check the RSL schema is consistent before any `.trlc` data
files exist.

---

## Example — `api-examples/filename-check/`

See the complete working example in
[`api-examples/filename-check/`](../api-examples/filename-check/).

---

## Multi-package layout

Chain packages with `deps` when one `.trlc` file imports another:

```python
# base/BUILD
trlc_specification(name = "spec", srcs = ["base.rsl"])
trlc_requirements(name = "reqs", srcs = ["base_reqs.trlc"], spec = [":spec"])

# feature/BUILD
trlc_requirements(
    name = "reqs",
    srcs  = ["feature_reqs.trlc"],
    spec  = [":feature_spec"],
    deps  = ["//base:reqs"],   # pulls in base.rsl + base_reqs.trlc
)
```
