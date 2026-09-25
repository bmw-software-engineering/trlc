# Disclaimer
This document does not replace a proper tool qualification in your
context. This document aims to guide you, and reduce the tool
qualification effort on your side.

TRLC, including this safety manual, is distributed in the hope that
it will be useful, but WITHOUT ANY WARRANTY; without even the
implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
PURPOSE. See the GNU General Public License for more details.

This document shall become a safety manual in the sense of ISO
26262 ("Road vehicles – Functional safety").
It might well apply to IEC 61508
("Functional Safety of Electrical/Electronic/Programmable
Electronic Safety-related Systems"), too.
However, the safety manual is incomplete as of today.


# Safety Manual
## Introduction
You shall follow the instructions given in this document in order to
qualify the TRLC tool for the following context:

This safety manual assumes you use the TRLC language and the TRLC tool for the following purpose:
- writing documents, especially requirement specification documents,
- using the TRLC tool in a CI (Continuous Integration) pipeline to
  ensure that the written document adheres to the TRLC language as
  specified in the Language Reference Manual.

where [version 3.0 of the LRM](https://bmw-software-engineering.github.io/trlc/lrm-3.0.html) applies.

Other purposes are not in the scope of this safety manual.

Note:
This safety manual does not apply to the Python API, although the
TRLC tool relies on the Python API.
The tool and the API are different things and need separate use
case analyses.
Here we consider only use cases of the tool.

## Definitions
The following definitions are given:
- TRLC files:
  all files created by the user that are given to the TRLC tool as
  input.
  The tool considers only files ending on `.trlc` and `.rsl`.
  Other files are ignored and are not considered input files.

## Instructions
### Version Control System
<!-- caused by ISO 26262-2 6.4.2.5 -->
You shall use a version control system to store all TRLC files.

Rationale:
Each TRLC object in a `.trlc` file has got an identifier.
The TRLC tool ensures that each identifier is unique.
But this uniqueness applies only to one moment in time, when the
TRLC tool runs.
TRLC Identifiers can be changed by the user.
Requirements shall have got a unique identifier throughout their
lifetime.
The commit identifier combined with the TRLC identifier provides
a mechanism to uniquely identify requirements during the whole
lifetime.

Example: Use [git](https://git-scm.com/).

### Always check the return code
Always check the return code of the TRLC tool.
It is not sufficient to analyze the command line output.

If the return code is non-zero, then there has been at least one error detected.
If there is no command line output, there may still be errors.

Rationale:
The command line output is not part of the tool qualification
strategy.
It will not be a qualified feature.
Only a tool return code of `0` shall guarantee that there are no
inconsistencies in the TRLC input files.

Note:
When using TRLC in a pipe, make sure to handle the return code of
TRLC.
Pipes only return the return code of the last program in the pipe.
If TRLC is not the last program, then by default the pipe will not
handle the TRLC return code.

### Validate Regular Expressions
If you use regular expressions (regex) in "check" statements,
then you shall qualify the Python function `re.match` against your
regex.
For this qualification you shall use the Python version which will
be used when running TRLC.

If you do so, we encourage you to contribute your particular
qualification to this repository, for example as a system test.

Rationale:
Qualifying `re.match` with arbitrary regular expressions is close
to impossible.

### Ensure exact input
You shall take measure to ensure that the given TRLC input files
represent the complete set of requirements.

Rationale:
If a TRLC file is not given as input to the TRLC tool, that file
might contain a duplicate definition of an identifier.
The TRLC tool will not detect that.

## Review Lookup
You shall provide a method to find the documented review of a given
requirement.

Example:
If you use GitHub pull requests to document reviews of requirements,
then you can use `git annotate` to find the pull requests (and
hence the reviews) related to a requirement.

## Recommendations
### Renaming
It is highly recommended not to rename TRLC identifiers.
This makes it easier to track changes of TRLC objects back in time
across several commits.

### GitHub Review Checklist
<!-- caused by ISO 26262-2 6.4.3.1 -->
It is highly recommended to use GitHub, and configure your CI system such that it inserts a checklist into the pull request's description whenever TRLC files are added, modified, or deleted.
The checklist shall guide the review of the requirements.
The checklist entries will be provided by your requirements
manager.

Rationale:
Using a checklist during reviews of requirements is mandatory by
several standards.

### Sanity Check for ASIL Inheritance
<!-- caused by ISO 26262-2 6.4.2.2 -->
It is highly recommended to install a CI job, that uses the
TRLC Python API (although currently not qualified), and checks
the inheritance of the ASIL attribute from one requirement to all its derived requirements.
The CI job shall forbid to merge a pull request which violates the
inheritance rule.

Example:
If requirement `Req1` is marked with `ASIL=B`, and requirement
`Req2` is derived from `Req1`, then `Req2` shall have an ASIL value
in compliance with the ASIL decomposition and inheritance rules.
In general, `Req2` shall have `ASIL=B` as well.
A CI job can enforce these rules.

### L.O.B.S.T.E.R.
<!-- caused by ISO 26262-2 6.4.3.2 -->
It is recommended to use
[LOBSTER](https://github.com/bmw-software-engineering/lobster)
- to ensure that all requirements are implemented,
- to provide a visual lookup table for all requirements.

Note:
You need to provide a usable search function to your requirements
engineers.
You can do that by using the TRLC API, by using L.O.B.S.T.E.R.,
or by some other means of (indexed) search function.
