# How to contribute to TRLC

## Did you find a bug?

* Ensure the bug was not already reported by searching
  [current issues](https://github.com/bmw-software-engineering/trlc/issues).

* If there is no existing report, please open a new one. Please
  include:
  * The version of TRLC (you can use `trlc --version` or `trlc --help` to
    find out).
  * A self-contained snippet of TRLC (including the `.rsl`) that triggers
    the bug.
  * Your expectation of correct behaviour.
 
## Questions

If you have questions about TRLC or the source code please do not open
issues. Instead use the 
[discussions forum](https://github.com/bmw-software-engineering/trlc/discussions).

## Contributing a change or fix

* Please read the relevant documentation before you make changes:
  * [Setting up your development environment](documentation/dev_setup.md)
  * [Architecture of TRLC](documentation/architecture.md)
  
* Please make sure that lint, test-all, and tracing do now show any new
  problems first.
  
* Open a PR. If you can reference a issue, please do so. Due to having to
  maintain the safety case we will never permit outside contributors to
  push directly.
  
* Make sure that any new features are also reflected in the LRM. The commit
  has to be atomic - LRM changes, code changes, doc changes, test changes,
  and tracability updates should be in a single commit.

* Please separate refactoring / code quality changes from feature changes
  (separate PRs).
