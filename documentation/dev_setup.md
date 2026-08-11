# Development environment setup

To contribute to TRLC, you will need to be able to run the
testsuite. Therefore you need GNU make and GNU findutils.
We do provide setup steps for Windows and Linux.
If you run into any problems on macOS, make sure you install
the latest GNU make version.

## Setup

* You need a suitable version of Python3 (3.8 <= Python3 <= 3.14). You
  can install this from your package manager. On Debian the package is
  called `python3`.

* You need to install the `cvc5` Python package (PyPI), or build it
  from source.

* You need to install everything from
  [requirements.txt](../requirements.txt).

* You also need to make available the relevant parts of lobster. You
  can do this in one of two ways:

  * Check out https://github.com/bmw-software-engineering/lobster and
    put the root of the repo on your `PYTHONPATH`.

  * Install from PyPI, carfully avoiding to install the TRLC
    dependency as that will make things really confusing:

    ```bash
    pip install bmw-lobster-core bmw-lobster-tool-python
    pip install --no-deps bmw-lobster-tool-trlc
	```

# Linux Setup

* You need GNU Make. This should be available on all sane GNU/Linux
  distributions. On Debian the package is called `build-essential`.

* You need to install Graphviz. On Debian the package is called
  `graphviz`.

# Windows Setup

* You need to Install Scoop.
  * Check out https://scoop.sh/

* Once Scoop is installed, install GNU findutils by running the following command:

  ```bash
  scoop install findutils
  ```

* you need to install GNU Make. You can do this by running the following command:

  ```bash
  scoop install make
  ```

* You need to install Graphviz.

  ```bash
  scoop install Graphviz
  ```

* You need to install coreutils.

  ```bash
  scoop install coreutils
  ```

## Important make targets

* `make lint` to run pycodestyle and pylint.

* `make test` to run most tests and show coverage analysis.

* `make test-all` to run all tests. This is the same as above, except
  we also include a massive test that takes a long time to
  run. Generally this is not worth it, but maybe do it once before you
  push.

* `make tracing` to build just the LOBSTER report.

* `make docs` to build all the documentation (including the LRM and
  the LOBSTER report).

## Code Formatting

```bash
# Check formatting — exits non-zero if any file would change
bazel run //:format.check

# Apply formatting in-place: ruff, buildifier and TRLC formatter
bazel run //:format.fix
```

## Code Linting

```bash
# Run all linters (pylint + ty) over every Python target
bazel build --config=lint //...
```

## Running system tests via Bazel

The system tests in `tests-system/` can be run as Bazel test
actions.  Test directories are discovered **automatically** via
`native.glob` — no manual list to maintain.

```bash
# Run all system tests (excludes "bulk")
bazel test //tests-system:fast

# Run all system tests including bulk
bazel test //tests-system:all_tests

# Run a single test directory
bazel test //tests-system:checks-1

```

### Adding a new system test

1. Create the directory `tests-system/<name>/` with the usual TRLC
   source files and golden files (`output`, `output.brief`,
   `output.json`; optionally `output.smtlib`).
2. If the test requires `--no-detailed-info` (or any other trlc flag),
   add an `options` file containing those flags (whitespace-separated).
   The test runner reads this file automatically — no BUILD change is
   needed.
3. Bazel picks up the new directory on the next build.  No changes to
   `tests-system/BUILD` are required.

### Running the large partial-loading tests via Bazel

The tests in `tests-large-partial/` exercise partial-loading of large
TRLC files:

```bash
# Run all partial tests
bazel test //tests-large-partial:partial_tests

# Run a single partial test
bazel test //tests-large-partial:partial-1
```

New partial tests are picked up automatically — just add a
`<name>.scenario` / `<name>.output` pair in `tests-large-partial/`.

## Coverage via Bazel

The system tests run trlc in-process as `py_test` targets, so Bazel can
instrument the trlc library code with `coverage.py` automatically.

```bash
# Collect coverage across all system tests and api-examples
bazel coverage //tests-system/...

# Render as HTML (requires lcov / genhtml)
genhtml "$(bazel info output_path)/_coverage/_coverage_report.dat" -o htmlcov
```

The `coverage` namespace in `.bazelrc` sets `--combined_report=lcov` and
`--instrumentation_filter=//trlc[/:]` so only the trlc library is measured.

## Formatter development

The TRLC formatter is a Prettier plugin in `tools/formatter/`.  It uses a
pure-JavaScript recursive-descent + Pratt expression parser — no native C
extension, no tree-sitter binding, and no `node-gyp` step.

### Prerequisites

The formatter is pure JavaScript, so no C toolchain or native addon build is
needed.  Bazel resolves all npm dependencies from `pnpm-lock.yaml` automatically.

For running unit tests locally outside Bazel you need Node.js (≥ 18):

```bash
cd tools/formatter
npm install
```

### Running formatter tests

```bash
# Unit tests (fast, JS only, node:test runner)
bazel test //tools/formatter:unit_test

# Integration tests (full pipeline: run prettier, diff against expected)
bazel test //tools/formatter/integration_test:all
```

### Check / fix TRLC source formatting

```bash
# Check — exits 123 if any .trlc/.rsl file needs reformatting
bazel run //tools/formatter:cmd-format-trlc-check

# Fix — rewrites all .trlc/.rsl files in-place
bazel run //tools/formatter:cmd-format-trlc
```

### Updating the parser

The TRLC grammar is encoded in the hand-written parser in
`tools/formatter/src/trlc-parser-impl.js` and tokenizer in
`tools/formatter/src/trlc-lexer.js`.  When the TRLC language gains a new
construct:

1. Add the new token kind(s) to `trlc-lexer.js` if needed.
2. Add the corresponding parse rule(s) to `trlc-parser-impl.js`.
3. Add the printer handler to the `NODE_PRINTERS` map in
   `tools/formatter/src/printer.js`.
4. Run the formatter tests to verify nothing regressed:
   ```bash
   bazel test //tools/formatter:unit_test //tools/formatter/integration_test:all
   ```
