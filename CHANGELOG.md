# TRLC Release Notes

## Language support

Up to date with version 2.5 of [TRLC language reference
manual](https://bmw-software-engineering.github.io/trlc/lrm.html).

## Limitations

The new `Markup_String` type currently has limited language support,
but we expect to add more features surrounding it later. (For example
quantifying over all references.)

## Changelog


### 1.0.14-dev



### 1.0.13

* [TRLC] Do not enter (sub-)directories named `bazel-*`. This
  behaviour can be turned off by using the new option
  `--include-bazel-dirs`.

* [TRLC] Add new option `--show-file-list` which dumps, on success,
  all files processed by the tool.

* [TRLC] Error messages now show all files relative to the current
  working directory.

### 1.0.12

* [TRLC, LRM] New type `Decimal` which allows you to specify values
  such as `0.1` with infinite precision. These are a subset of
  rational numbers.

* [TRLC, LRM] New implicitly declared built-in functions `Integer` and
  `Decimal` which can be used to convert a value to an `Integer` and
  `Decimal` respectively. The language does not support implicit
  conversion, you will have to make sure all types are converted
  correctly yourself.

* [TRLC, LRM] new type `Markup_String` which is a special kind of
  `String` that behaves in exactly the same way. However you reference
  other TRLC records directly: `for example see [[potato,
  package.wibble]]`. These references are checked and validated by
  TRLC.

### 1.0.11

* [TRLC] You can now provide more than one directory on the
  command-line to process, as well as individual files. If no files or
  directories are provided the default is now to analyse the currenty
  directory `.` including all sub-directories.

* [TRLC] In error messages that reference another file+location more
  of the path is now shown to help you find the problem. For example
  instead of `previous definition at foo.rsl:1` you now would get
  `previous definition at potato/foo.rsl:1`.

### 1.0.10

* [TRLC] Fix issue where TRLC could sometimes return 0 instead of 1 if
  there were non-fatal errors.

* [TRLC] Fix missing array length checks. Arrays now correctly have
  their desired size enforced.

### 1.0.9

* [LRM] The LRM for TRLC is [now written in
  TRLC](https://github.com/bmw-software-engineering/trlc/tree/main/language-reference-manual). There
  is also a [HTML
  version](https://bmw-software-engineering.github.io/trlc/lrm.html)
  available for easier reading. During conversion we fixed a number of
  issues in the LRM (missing keywords, etc.) and made a few cleanups
  and simplifications; however the language and its semantics have not
  changed.

* [LRM, TRLC] Add support for existential quantification. This
  introduces a new keywords `exists`.

* [LRM, TRLC] Also permit `in` and `not in` for arrays. This is a
  convenient short-cut for existential quantification over an array to
  test for membership.

* [LRM, TRLC] Fix oversight in the LRM, not allowing `true` and
  `false` to appear as values.

### 1.0.8

* [TRLC] Fix ICE when attempting to parse completely empty files.

* [LRM, TRLC] Two minor improvements for the handling of triple quoted
  strings: empty lines are now ignored when removing common leading
  whitespace, and trailing whitespace is stripped.

### 1.0.7

* [TRLC] Implement missing feature: integer values in record
  declarations can be prefixed by a unary `+` or `-`.

* [TRLC] Make parse order of files more predictable (which also makes
  error messages more predictable) and not so dependent on filesystem
  ordering.

### 1.0.6

* [LRM, TRLC] Support declarations of checks in the `.rsl` files. This
  means you don't need to have a separate check file, allowing you to
  implement your process or business logic closer to the type
  declarations. Dedicated check files continue to be supported.

* [LRM, TRLC] Rework builtin functions to not have the ugly `trlc:`
  prefix. Builtin functions now look more natural, e.g. `len` instead
  of `trlc:len`. The legacy functions will remain as a deprecated
  feature, and we'll remove them at a future date.

* [TRLC] Fix bug in array parsing and evaluation.

* [TRLC] Add the first two checks to the `--lint` option: one about
  misleading unary operators, and another on using deprecated
  functions.

* [TRLC] Fix a bug where a record reference to a type extension
  instead of the base type was not permitted, when it should be.

### 1.0.5

* [TRLC] Add `--brief` mode intended for CI. Expand tutorial to
  explain how it works.

* [TRLC] Add two new API functions (a [simpler
  lookup](https://bmw-software-engineering.github.io/trlc/manual/ast.html#trlc.ast.Symbol_Table.lookup_assuming)
  and [inheritence
  checking](https://bmw-software-engineering.github.io/trlc/manual/ast.html#trlc.ast.Record_Type.is_subclass_of)
  for record types).

### 1.0.4

* [LRM, TRLC] First public release
