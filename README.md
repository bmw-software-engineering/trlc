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
* [User manual: TRLC linter](documentation/linter.md) (the user manual for the TRLC static analysis and linter)
* [Release Notes](CHANGELOG.md) (read this to find out whats new)
* [License](LICENSE)

### For advanced users

* [Language Reference Manual](https://bmw-software-engineering.github.io/trlc/lrm.html)
  (for language lawyers)
* [Python API Documentation](https://bmw-software-engineering.github.io/trlc/)
  (API reference for end-users)
* [Iteration API by Section Documentation](https://bmw-software-engineering.github.io/trlc/section_api.html)
  (API reference for end-users)
* [AST Hierarchy](https://bmw-software-engineering.github.io/trlc/ast_hierarchy.svg)
  (overview over all classes in the AST)

### For TRLC developers

* [Set up development environment](documentation/dev_setup.md)
* [Lexer/Parser Hierarchy](https://bmw-software-engineering.github.io/trlc/parser_hierarchy.svg)
  (overview over all classes releated to the lexing and parsing of TRLC)
* [Tool Architecture Overview](documentation/architecture.md)
* [TRLC Static Checker Slides](https://bmw-software-engineering.github.io/trlc/linter.pdf) (Kinda incomplete, designed to go along with a code walkthrough)
* [Requirements Coverage Report](https://bmw-software-engineering.github.io/trlc/tracing.html)
* [Code Coverage Report](https://bmw-software-engineering.github.io/trlc/htmlcov/index.html)

## Dependencies

### Run-time
* 3.8 <= Python3 <= 3.11
* [PyVCG](https://pypi.org/project/PyVCG)

Optional dependencies (they are not installed automatically):
* [PyPI CVC5](https://pypi.org/project/cvc5) (Linux or OSX only,
  required when using the `--verify` option)
* [Binary CVC5](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.0.8)
  (An alternative to PyPI CVC5, make sure to rename the binary to
  `cvc5` and put it on your PATH).
