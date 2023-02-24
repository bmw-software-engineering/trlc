# Treat Requirements Like Code (TRLC)
TRLC is a domain-specific language developed at BMW for writing (and
linking) requirements with meta-data.

The repository contains:

* The [language reference
  manual](https://bmw-software-engineering.github.io/trlc/lrm.html)
  for TRLC.

* A pure Python reference implementation of TRLC.

The implementation is not very fast, but designed to be pedantically
correct in following the language definition.  Eventually it will also
contain a powerful linter to find issues with types and check
rules.

The Python implementation can be used for several purposes:

* It can be used to validate other TRLC implementations.

* It can be used to validate a body of requirements (e.g. a CI check
  that all requirements are well formed)

* The API can be used to write other tools based on TRLC (for example
  a tool to render the requirements in HTML, a tool to diff
  requirements or perform an impact analysis, or a tool to perform
  software traceability, etc.)

## Documentation

* [Tutorial](TUTORIAL.md) (read this as a first introduction)
* [Release Notes](CHANGELOG.md) (read this to find out whats new)
* [Python API Documentation](https://bmw-software-engineering.github.io/trlc/)
  (user guide for using the API)
* [Language Reference Manual](https://bmw-software-engineering.github.io/trlc/lrm.html)
  (for language lawyers)
* [License](LICENSE)

## Dependencies

### Run-time
* Python3 >= 3.7

### Development tools
* GNU Make
* [PyCodeStyle](https://pypi.org/project/pycodestyle/) (from PyPI, for
  basic checking of source code style)
* [PyLint](https://pypi.org/project/pylint/) (from PyPI, for basic bug
  finding)
* [Coverage](https://pypi.org/project/coverage/) (from PyPI, to
  perform branch coverage when running the test suite)
* [Sphinx](https://pypi.org/project/Sphinx/) (from PyPI, for building
  the documentation)
