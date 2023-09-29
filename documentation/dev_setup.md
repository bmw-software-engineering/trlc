# Development environment setup

To contribute to TRLC you will need to be able to run the
testsuite. Currently this is only realistic on GNU/Linux, although it
may be possible to get it to work on other platforms.

## Setup

* You need a suitable version of Python3 (3.8, 3.9, 3.10, or
  3.11). The reason we do not support 3.12 or later (for the dev
  setup) is the dependency on CVC5. Users could use 3.12; but they
  won't be able to use the CVC5 API.

* You also need an executable `cvc5` binary on your PATH. Download the
  appropriate version from
  https://github.com/cvc5/cvc5/releases/tag/cvc5-1.0.8 and rename
  it. You can also build CVC5 from source if there is no pre-built
  release available for your platform.

* You need to install the `cvc5` PyPI package, or build it from
  source.

* You need GNU Make. This should be available on all sane GNU/Linux
  distributions. On Debian the package is called `build-essential`.

* You need to install Graphviz. On Debian the package is called
  `graphviz`.

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
