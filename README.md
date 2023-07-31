# Treat Requirements Like Code (TRLC)
TRLC is a domain-specific language developed at BMW for writing (and
linking) requirements with meta-data.

The repository contains:

* The [language reference
  manual](https://bmw-software-engineering.github.io/trlc/lrm.html)
  for TRLC. [Previous versions](documentation/LRM.md) are also available.

* A pure Python reference implementation of TRLC.

The implementation is not very fast, but designed to be pedantically
correct in following the language definition. The tools also include a
powerful static analysis tool to find issues with types and
user-defined check rules.

The Python implementation can be used for several purposes:

* It can be used to validate other TRLC implementations.

* It can be used to validate a body of requirements (e.g. a CI check
  that all requirements are well formed)

* The API can be used to write other tools based on TRLC (for example
  a tool to render the requirements in HTML, a tool to diff
  requirements or perform an impact analysis, or a tool to perform
  software traceability, etc.)

## Documentation

### For normal users

* [Tutorial](documentation/TUTORIAL.md) (read this as a first introduction)
* [Release Notes](CHANGELOG.md) (read this to find out whats new)
* [License](LICENSE)

### For API users

* [Language Reference Manual](https://bmw-software-engineering.github.io/trlc/lrm.html)
  (for language lawyers)
* [Python API Documentation](https://bmw-software-engineering.github.io/trlc/)
  (API reference for end-users)
* [AST Hierarchy](https://bmw-software-engineering.github.io/trlc/ast_hierarchy.svg)
  (overview over all classes in the AST)

### For TRLC developers

* [Lexer/Parser Hierarchy](https://bmw-software-engineering.github.io/trlc/parser_hierarchy.svg)
  (overview over all classes releated to the lexing and parsing of TRLC)
* [Tool Architecture Overview](documentation/architecture.md)

## Dependencies

### Run-time
* 3.8 <= Python3 <= 3.10

Optional dependencies (they are not installed automatically):
* [PyVCG](https://pypi.org/project/PyVCG) (Linux or OSX only, required
  when using the `--verify` option)

### Development tools
* GNU Make
* Graphviz
* [PyCodeStyle](https://pypi.org/project/pycodestyle) (from PyPI, for
  basic checking of source code style)
* [PyLint](https://pypi.org/project/pylint) (from PyPI, for basic bug
  finding)
* [Coverage](https://pypi.org/project/coverage) (from PyPI, to
  perform branch coverage when running the test suite)
* [Sphinx](https://pypi.org/project/Sphinx) (from PyPI, for building
  the documentation)
* [PyVCG](https://pypi.org/project/PyVCG) (from PyPI, for building
  verification conditions)
* [CVC5](https://pypi.org/project/cvc5) (from PyPI, for discharging
  verification conditions)

You can install all Python dependencies by doing:

```bash
pip3 install -r requirements.txt
```

When building the traceability report you also need to install two
lobster packages. Since there is a circular dependency, please install
like this:

```bash
pip3 install bmw-lobster-core bmw-lobster-tool-python
pip3 install --no-deps bmw-lobster-tool-trlc
```

The most important make targets when developing TRLC are:

* `lint` (runs pycodestyle and pylint)
* `test` (performs unit and system tests and shows coverage)
* `tracing` (generates traceability report)
