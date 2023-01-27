# TRLC Tutorial (Installing)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## Installing the tools

The easiest way to install the tools is through PyPI:

```
$ pip3 install --user trlc
```

There are currently no dependencies, all you need is a moderatly
recent Python 3.7.

Don't forget to adjust your `PATH` so that `.local/bin` (or the
equivalent on Windows) is on it; so that the `trlc` executable can be
run.

Note that the above just installs command-line tools and the Python
API. There is no IDE integration yet.

## From source (not recommended)

You can also run the tools directly from a git checkout:

* Put the root of the repo on your `PATH`.
* Put the root of the repo on your `PYTHONPATH`.

## Test if things are working

To check if the main program works:

```
$ trlc --help
```

(If you run from source, the main program is called trlc.py instead.)

To check if the API is working start a Python interpreter and do:

```
from trlc.version import TRLC_VERSION
print(TRLC_VERSION)
```

This should print the current TRLC version string matching what
`trlc --help` prints.
