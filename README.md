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

### Language note

In a `.rsl` file, a type may be used before the place where it is
declared in the same file. This is allowed for:

* the type of a record component,
* the type of a tuple field, if that type is a record,
* a record type used as a member of a union type.

Example:

```rsl
package demo

type Requirement {
  position Coordinate
}

tuple Coordinate {
  x Integer
  y Integer
}
```

This is valid: `Requirement` uses `Coordinate` before the line that declares it.

The following are not supported:

* A tuple field that refers to a tuple declared later in the file. This
  includes mutually recursive tuples (`A` contains `B`, `B` contains
  `A`). Declare the inner tuple first.
* A record that extends a type declared later in the file. Declare
  the base type earlier.
* A check that uses a field of a record type declared after the check.
  Declare the record type first.

Note:

* Tuples remain acyclic (because they are inline objects)
* Type inheritance graph remains acyclic
* Package import graph remains acyclic

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
* [Bazel integration](documentation/TUTORIAL-BAZEL.md) (how to use TRLC inside a Bazel build)
* [User manual: TRLC linter](documentation/linter.md) (the user manual for the TRLC static analysis and linter)
* [Release Notes](CHANGELOG.md) (read this to find out what’s new)
* [License](LICENSE)

### For advanced users

* [Language Reference Manual](https://bmw-software-engineering.github.io/trlc/lrm.html)
  (for language lawyers)
* [Python API Documentation](https://bmw-software-engineering.github.io/trlc/)
  (API reference for end-users)
* [AST Hierarchy](https://bmw-software-engineering.github.io/trlc/ast_hierarchy.svg)
  (overview over all classes in the AST)

### For TRLC developers

* [Set up development environment](documentation/dev_setup.md)
* [Lexer/Parser Hierarchy](https://bmw-software-engineering.github.io/trlc/parser_hierarchy.svg)
  (overview over all classes related to the lexing and parsing of TRLC)
* [Tool Architecture Overview](documentation/architecture.md)
* [TRLC Static Checker Slides](https://bmw-software-engineering.github.io/trlc/linter.pdf) (Kinda incomplete, designed to go along with a code walkthrough)
* [Requirements Coverage Report](https://bmw-software-engineering.github.io/trlc/tracing.html)
* [Code Coverage Report](https://bmw-software-engineering.github.io/trlc/htmlcov/index.html)

### Tools Available

* [TRLC_RST](tools/trlc_rst/README.md): Convert TRLC Requirements for Sphinx Build
* [Converters](https://github.com/NewTec-GmbH/pyTRLCConverter): Multiple converters from TRLC to other file formats. The tool suite is maintained by [NewTec GmbH](https://www.newtec.de/).

## Dependencies

### Run-time
* 3.10 <= Python3 <= 3.14
* [PyVCG](https://pypi.org/project/PyVCG)
* [PyPI CVC5](https://pypi.org/project/cvc5)(GNU/Linux only)
  (required when using the `--verify` option)

## Acknowledgements

Special thanks to [Florian Schanda](https://github.com/florianschanda)
for his many valuable contributions to this repository.
