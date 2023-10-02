# TRLC Tutorial (Installing)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## Installing the tools

The easiest way to install the tools is through PyPI:

```
$ pip3 install --user trlc
```

There are currently one required dependencies (PyVCG which should be
installed automatically), all you need is a moderatly recent Python
3.8 / 3.9 / 3.10 / 3.11.

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

```python
from trlc.version import TRLC_VERSION
print(TRLC_VERSION)
```

This should print the current TRLC version string matching what
`trlc --help` prints.

## Editor / IDE Integration

### EMACS

You can paste this in your `.emacs` file to have some basic support
for TRLC. This is a bit of a hack and not a real language support, but
it is better than nothing.

```emacs
(defvar trlc-keywords
  '("abs"
    "abstract"
    "and"
    "checks"
    "else"
    "elsif"
    "enum"
    "error"
    "exists"
    "extends"
    "false"
    "fatal"
    "final"
    "forall"
    "freeze"
    "if"
    "implies"
    "import"
    "in"
    "not"
    "null"
    "optional"
    "or"
    "package"
    "section"
    "separator"
    "then"
    "true"
    "tuple"
    "type"
    "warning"
    "xor"))

(defvar trlc-types
  '("Markup_String"
    "String"
    "Integer"
    "Decimal"
    "Boolean"))

 (defvar trlc-font-lock-defaults
   `((
      ( ,(regexp-opt trlc-keywords 'words) . font-lock-keyword-face)
      ( ,(regexp-opt trlc-types 'words) . font-lock-builtin-face)
      )))

(define-derived-mode trlc-mode js-mode "TRLC"
  "TRLC mode is a major mode for editing TRLC files"

  (setq font-lock-defaults trlc-font-lock-defaults)
  (setq js-indent-level 2)
  (setq fill-column 60)

  )

(provide 'trlc-mode)
(add-hook 'trlc-mode-hook 'flyspell-mode)
(add-hook 'trlc-mode-hook 'flyspell-buffer)

(add-to-list 'auto-mode-alist '("\\.rsl\\'" . trlc-mode))
(add-to-list 'auto-mode-alist '("\\.check\\'" . trlc-mode))
(add-to-list 'auto-mode-alist '("\\.trlc\\'" . trlc-mode))
```
