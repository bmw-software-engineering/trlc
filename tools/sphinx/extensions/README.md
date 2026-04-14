# Sphinx Extensions

Custom Sphinx extensions used when building TRLC-based documentation.

## `trlc` — requirement domain

**Location:** `trlc/trlc.py`

A Sphinx domain that makes `.. requirement:definition::` blocks (as produced by
[`trlc_rst`](../../trlc_rst/README.md)) first-class Sphinx objects.

### Features

- **`.. requirement:definition:: <name>`** — registers a requirement with a
  stable HTML anchor (`requirement-<name>`) so it can be linked to from
  anywhere in the documentation.
- **`:requirement:upstream-ref:`** / **`:requirement:downstream-ref:`** — roles
  for cross-referencing a requirement by its fully-qualified name
  (e.g. `MyProject.REQ_001`). A warning is emitted if the target is not found
  or is ambiguous.
- **Requirement Index** — an auto-generated index page listing every defined
  requirement in alphabetical order, grouped by first letter.

### Bazel usage

```python
load("@trlc_sphinx_dependencies//:requirements.bzl", "requirement")

py_library(
    name = "trlc",
    srcs = ["trlc.py"],
    imports = ["."],
    deps = [requirement("sphinx")],
)
```

Add the library to the `deps` of your `sphinx_build` target and register the
extension in `conf.py`:

```python
extensions = [
    "trlc",
]
```
