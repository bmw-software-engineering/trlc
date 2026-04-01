# TRLC RST

The TRLC RST converts requirements written in TRLC into
reStructuredText (RST). The generated RST files can be consumed by Sphinx
to produce HTML or PDF documentation.

## Using the converter

### Example

Given `schema.rsl`:

```
package MyProject

type Requirement {
    description optional String
}
```

And `requirements.trlc`:

```
package MyProject

Requirement REQ_001 {
    description = "The system shall process inputs correctly"
}

Requirement REQ_002 {
    description = "The system shall produce correct outputs"
}
```

The converter produces:

```rst
Requirements
============
.. requirement:definition:: MyProject.REQ_001

   The system shall process inputs correctly

.. requirement:definition:: MyProject.REQ_002

   The system shall produce correct outputs

```

### Supported RST formatting in descriptions

The following formatting is supported in requirement `description` fields:

| Syntax | Example | Output |
|---|---|---|
| Bold | `**text**` | **bold** (RST native) |
| Italic | `*text*` | *italic* (RST native) |
| Inline code | ` ``code`` ` | `code` (RST native) |
| Hyperlink | `[label](url)` | RST `` `label <url>`_ `` |
| Code block | line ending with `::` followed by indented content | RST literal block |
| Bullet list | lines starting with `-` | RST bullet list |
| Numbered list | lines starting with `1.`, `2.`, … | RST enumerated list |
| Line breaks | any non-empty line | separated by blank lines in RST |

### Command-line Usage

```bash
python trlc_rst.py --input-dir path/to/trlc/files --output output.rst
```

| Option | Description |
|---|---|
| `-i` / `--input-dir` | Directory scanned recursively for `.rsl` and `.trlc` files (default: `.`) |
| `-o` / `--output` | Path of the RST file to write (required) |
| `-s` / `--source-files` | Space-separated list of `.trlc` files to render. All other files are still parsed for dependency resolution but are not included in the output. |
| `-t` / `--title` | Section title written at the top of the output file (default: `Requirements`). Pass an empty string to omit the title entirely. |

### Bazel Usage

Load the `trlc_rst` rule from `//:trlc.bzl` and pass the TRLC
requirement targets as `reqs`:

```python
load("//:trlc.bzl", "trlc_rst", "trlc_requirements", "trlc_specification")

trlc_specification(
    name = "spec",
    srcs = ["schema.rsl"],
)

trlc_requirements(
    name = "reqs",
    srcs = ["requirements.trlc"],
    spec = [":spec"],
)

trlc_rst(
    name = "requirements_rst",
    reqs = [":reqs"],
)
```

The rule produces a single `<name>.rst` file in the Bazel output tree.

An optional `title` attribute controls the top-level heading (default:
`"Requirements"`). Pass an empty string to omit the heading entirely:

```python
trlc_rst(
    name = "requirements_rst",
    reqs = [":reqs"],
    title = "",
)
```

## Integrating the renderer from another repository

Assuming you have already added `trlc` as a Bazel module dependency (see the
TRLC documentation for details), you can use the renderer directly. The
`trlc_dependencies` pip hub — which provides `bigtree` — is part of the `trlc`
module and is available to your workspace automatically; no additional pip hub
setup is required.

Load the rule from `@trlc//:trlc.bzl`:

```python
load("@trlc//:trlc.bzl", "trlc_rst", "trlc_requirements", "trlc_specification")

trlc_specification(
    name = "spec",
    srcs = ["schema.rsl"],
)

trlc_requirements(
    name = "reqs",
    srcs = ["requirements.trlc"],
    spec = [":spec"],
)

trlc_rst(
    name = "requirements_rst",
    reqs = [":reqs"],
)
```

## Developer notes

### Architecture

`TRLC RST` (in `trlc_rst.py`) processes input in three steps:

1. **Parse** — `parse_trlc_files()` hands the input directory to the TRLC
   `Source_Manager`, which resolves all `.rsl` specs and `.trlc` requirement
   files and returns a `Symbol_Table`.

2. **Build tree** — `convert_symbols_to_tree()` iterates over every
   `Record_Object` in the symbol table and inserts it into a `bigtree` node
   tree. Section hierarchy from the TRLC source is preserved: shared section
   nodes are reused so that two requirements under the same section end up as
   siblings rather than in separate subtrees.

3. **Render** — `render_to_file()` walks the tree with `preorder_iter`.
   Non-leaf nodes (sections) become RST headings; leaf nodes (requirements)
   become `.. requirement:definition::` directives. Description fields are
   post-processed by `_preprocess_description()` which converts Markdown-style
   links to RST and adds correct indentation for directive content.

The `trlc_rst` Bazel rule (in `trlc_rst.bzl`) wraps the binary and
lets other targets declare a rendered RST file as a build output.

### System tests

Tests live in `tests/`. Each subdirectory is one test case and must contain:

- one or more `.rsl` schema files
- one or more `.trlc` requirement files
- `output.rst` — the golden file the renderer output is diffed against

Run all tests:

```bash
bazel test //tools/trlc_rst/tests:all
```

Run a single test case:

```bash
bazel test //tools/trlc_rst/tests:simple-flat
```

**Adding a new test case:**

1. Create a subdirectory under `tests/`, e.g. `tests/my-new-case/`.
2. Add `.rsl` and `.trlc` input files.
3. Generate the golden file by running the renderer directly:
   ```bash
   python tools/trlc_rst/trlc_rst.py \
       --input-dir tools/trlc_rst/tests/my-new-case \
       --output tools/trlc_rst/tests/my-new-case/output.rst
   ```
4. Review `output.rst`, then commit it alongside the input files.

The `tests/BUILD` file discovers test cases automatically via
`glob(["*/output.rst"])` — no manual registration is needed.

