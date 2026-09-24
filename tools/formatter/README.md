# TRLC Formatter

A [Prettier](https://prettier.io/) plugin that formats `.trlc` (requirements)
and `.rsl` (metamodel) files.

The formatter uses a pure-JavaScript recursive-descent + Pratt expression
parser (`src/trlc-parser-impl.js`) — no native C extension, no tree-sitter
binding, and no `node-gyp` step is required at runtime or build time.
Because parsing is grammar-driven rather than regex-based, string and comment
content is preserved exactly, and files with syntax errors are returned
unchanged (never corrupted).

Architecture:

- `src/trlc-lexer.js` — hand-written tokenizer; emits a flat token array.
- `src/trlc-node.js` — `CSTNode` class; mirrors the tree-sitter `SyntaxNode`
  API surface so `printer.js` works without modification.
- `src/trlc-parser-impl.js` — recursive-descent + Pratt expression parser;
  produces a `CSTNode` tree.
- `src/parser.js` — Prettier parser entry point; delegates to
  `trlc-parser-impl.js`.
- `src/printer.js` — walks the `CSTNode` tree and emits a Prettier document.
- `src/options.js` — declares the `trlcNormalizeAttributes`,
  `trlcAttributeGap`, and `trlcSortImports` custom options.

---

## Running the formatter in this repo

All commands are run from the workspace root.

### Check which files need formatting

```bash
bazel run //tools/formatter:cmd-format-trlc-check
```

Prints every `.trlc`/`.rsl` file whose content differs from what the formatter
would produce. Exits with code 123 if any files need reformatting — suitable
for CI.

### Format all files in-place

```bash
bazel run //tools/formatter:cmd-format-trlc
```

Rewrites all `.trlc`/`.rsl` files in the workspace.

### Format a single file (preview only)

```bash
bazel run //tools/formatter:prettier_trlc_formatter -- /absolute/path/to/file.trlc
```

Outputs the formatted content to stdout without modifying the file.

### Run the tests

```bash
# Integration tests (full Prettier pipeline, diff against expected output)
bazel test //tools/formatter/integration_test:all

# Unit tests (format a snippet and assert the result)
bazel test //tools/formatter:unit_test
```

---

## Integrating the formatter in another Bazel repo

The formatter is consumed as a Bazel module dependency — no file copying
required.

### Step 1 — Declare the module dependency

In your `MODULE.bazel`, add `trlc` as a dependency and point it at this
repository. Until the module is published to a registry, use `git_override`:

```starlark
bazel_dep(name = "trlc", version = "0.0.0")
git_override(
    module_name = "trlc",
    commit = "<commit-sha>",
    remote = "https://github.com/bmw-software-engineering/trlc.git",
)
```

Also add the transitive requirements that this module needs
(if your repo does not already declare them):

```starlark
bazel_dep(name = "aspect_rules_js",   version = "2.9.2")
bazel_dep(name = "aspect_rules_lint", version = "2.2.0")
bazel_dep(name = "rules_multirun",    version = "0.13.0")
```

`aspect_rules_lint` must be patched to recognise the `TRLC` language. Copy
`third_party/format/add_trlc_support.patch` from this repo into your own
`third_party/format/` directory and add:

```starlark
single_version_override(
    module_name = "aspect_rules_lint",
    patch_strip = 1,
    patches = ["//third_party/format:add_trlc_support.patch"],
)
```

> **Note** — `single_version_override` and `git_override` are only allowed in
> the root module of a workspace. They must live in your repo's own
> `MODULE.bazel`, not inside a dependency.

### Step 2 — Use the formatter target

The formatter binary is exposed at:

```
@trlc//tools/formatter:prettier_trlc_formatter
```

#### Run it directly on a single file

```bash
bazel run @trlc//tools/formatter:prettier_trlc_formatter -- /absolute/path/to/file.trlc
```

#### Create a `format_multirun` in your own repo

In any `BUILD` file in your repo (e.g. the root `BUILD`):

```starlark
load("@aspect_rules_lint//format:defs.bzl", "format_multirun")

format_multirun(
    name = "format",
    python   = "@aspect_rules_lint//format:ruff",          # example — adjust to your stack
    rust     = "@rules_rust//tools/upstream_wrapper:rustfmt",
    starlark = "@buildifier_prebuilt//:buildifier",
    trlc     = "@trlc//tools/formatter:prettier_trlc_formatter",
)
```

Then:

```bash
bazel run //:format.fix   # fix all files in-place
bazel run //:format.check # CI check — exits 123 if any file needs reformatting
```

#### Split check/fix pipelines with `multirun`

If you keep separate fix and check pipelines:

```starlark
load("@rules_multirun//:defs.bzl", "command", "multirun")

command(
    name = "cmd-format-trlc",
    command = "@trlc//tools/formatter:format",
    run_from_workspace_root = True,
)

command(
    name = "cmd-format-trlc-check",
    command = "@trlc//tools/formatter:format.check",
    run_from_workspace_root = True,
)

multirun(
    name = "format_all",
    commands = [
        ":cmd-format-lint",       # Python / Rust / Starlark
        ":cmd-format-trlc",       # TRLC / RSL
    ],
    jobs = 0,
)

multirun(
    name = "format_all.check",
    commands = [
        ":cmd-format-lint-check",
        ":cmd-format-trlc-check",
    ],
    jobs = 0,
)
```

---

## Formatter options

The following Prettier options can be set in `prettier.config.mjs`:

| Option | Type | Default | Description |
|---|---|---|---|
| `trlcNormalizeAttributes` | boolean | `true` | Apply R08: align type tokens across all fields in a type/tuple block to the same column (snapped to the nearest `tabWidth` multiple). Set to `false` to preserve source spacing verbatim. |
| `trlcAttributeGap` | number | `2` | Minimum spaces between the longest field name and the type column before snapping to the nearest `tabWidth` multiple (R08). |
| `trlcSortImports` | boolean | `true` | Sort consecutive `import` statements alphabetically, case-insensitive (R05). Set to `false` to preserve source order. |
| `tabWidth` | number | `4` | Indent width in spaces (R01). |
| `useTabs` | boolean | `false` | Use tab characters instead of spaces (R01). |

Example `prettier.config.mjs` with custom settings:

```js
export default {
  plugins: ["./src/index.js"],
  overrides: [
    {
      files: ["*.trlc", "*.rsl"],
      options: {
        parser: "trlc",
        tabWidth: 4,
        trlcNormalizeAttributes: true,
        trlcSortImports: true,
      },
    },
  ],
};
```
