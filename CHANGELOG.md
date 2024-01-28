# TRLC Release Notes

## Language support

Up to date with version 2.9 of [TRLC language reference
manual](https://bmw-software-engineering.github.io/trlc/lrm.html).

## Limitations

The new `Markup_String` type currently has limited language support,
but we expect to add more features surrounding it later. (For example
quantifying over all references.)

The `--verify` feature has several limitations that can create false
alarms and cause inaccurate or impossible counter-examples to be
generated in the following situations:

* Decimal numbers may generate real or irrational examples.
* Quantifiers.
* Tuples in arrays.
* Markup_Strings are treated just like strings (i.e. they do not carry
  a constraint yet about legal syntax of inline references).
* The builtin `matches` function.

## Changelog


### 1.2.3-dev

* [TRLC] New command-line flag `-I` which can be used to register
  include directories. You can use this to automatically parse a
  minimal set of file. Normally when invoking eg `trlc foo.trlc` this
  will fail, because you did not provide e.g. `foo.rsl`.

  With the `-I` flag you can now automatically let the tool discover
  any dependencies. When using e.g. `trlc -I . foo.trlc` the tool will
  discover it also needs `foo.rsl` and maybe `potato.rsl` which you
  imported in `foo.trlc`.

  Especially in large projects this will be much faster than
  explicitly parsing everything.

* [API] The source manage has a new function
  [register_include](https://bmw-software-engineering.github.io/trlc/manual/infrastructure.html#trlc.trlc.Source_Manager.register_include)
  which should be used before any `register_file` or `register_dir`
  calls.

* [API] *When using includes*, the symbol table will contains packages
  for every discovered package. These are indistinguisable from normal
  (but empty) packages, so if you're relying on iterating over all
  known packages you will find a lot of unused and empty ones now. If
  the include mechanism is not used, then there is no change in
  behaviour.

* [TRLC] Various performance improvements when parsing large files.

* [TRLC] Add `--version` flag that can be used to figure out the
  installed TRLC version.

* [TRLC] Fix bug when creating a lexer with an empty file with
  delivered file content. The lexer attempted to open the file instead
  of using the empty string passed to the constructor.

* [TRLC] Fix a bug in the verifier mistranslating existential
  quantifiers. This could both lead to false alarms and missed bugs.

### 1.2.2

* [API] Add callbacks to the
  [Source_Manager](https://bmw-software-engineering.github.io/trlc/manual/infrastructure.html#trlc.trlc.Source_Manager)
  to notify clients of the parse progress.

### 1.2.1

* [TRLC] New minor version release due to minor API changes and major
  command-line changes.

* [TRLC] When using `--verify` you can now also specify a
  [CVC5](https://github.com/cvc5/cvc5) executable using
  `--use-cvc5-binary`. This allows you to use the `--verify` option on
  platforms where there is no CVC5 PyPI package (i.e. Windows or more
  recent versions of OSX).

* [TRLC] The [PyVCG](https://pypi.org/project/PyVCG) package is now required
  on all platforms. The optional dependency is now
  [CVC5](https://pypi.org/project/cvc5) instead.

* [TRLC] Remove the `--lint` option. Lint messages are now enabled by
  default, and `.trlc` files are processed as well. Instead there is a
  `--no-lint` option which turns off the extra warnings.

* [TRLC] Add the `--skip-trlc-files` option which disables processing
  of `.trlc` files. Enabling this option is equivalent to the old
  `--lint` mode.

* [TRLC] Add the `--error-on-warnings` option which generates a status
  code of 1 if any warning is raised.

* [TRLC] We now always print a short summary, indicating how many
  files were processed and how many messages were generated. The
  `--show-file-list` option still exists and still prints the complete
  list of files. This summary may be suppressed with the `--brief`
  option.

* [API] The
  [Source_Manager](https://bmw-software-engineering.github.io/trlc/manual/infrastructure.html#trlc.trlc.Source_Manager)
  has new and different constructor flags, although it can still be
  constructed with no parameters.

* [API] The
  [Message_Handler](https://bmw-software-engineering.github.io/trlc/manual/errors.html#trlc.errors.Message_Handler)
  now uses an enumeration instead of a string to signal message
  severity/kind. For normal use this is transparent, but if you
  subclass the message handler then you need to deal with this. The
  category (for lint messages) is now also a separate parameter
  instead of being baked into the message.

* [TRLC] Please note that if you parse messages in CI, the [regex has
  changed
  slightly](https://github.com/bmw-software-engineering/trlc/blob/main/documentation/TUTORIAL-CI.md#parsing-the-output).

* [TRLC] Fix an issue where `--skip-trlc-files` would incorrectly
  register and parse the preamble of `.trlc` files.

* [TRLC] Fix a spurious space in the summary output.

* [TRLC] Fix support for Python 3.11. The package can now be installed
  without issues.

* [TRLC] Fix issue in VCG where the matches function could be
  generated more than once. This was only an issue in the debug output
  and was not visible to users.

### 1.1.10

* [TRLC] Fix missing typechecks for numeric subtypes on value
  assignments. It was possible to assign an integer to a decimal
  component, or the other way around. This now correctly generates an
  error.

* [TRLC, LRM] You can now also write `"""foo"""` string literals. Just
  like the `'''` strings, these can contain newlines.

* [TRLC, LRM] User defined checks are now not allowed to contain a
  newline. However you can now provide additional information that
  _can_ contain a newline. For example:

  ```trlc
  checks Requirement {
    top_level == true or derived_from != null,
      error "linkage incorrect",
      """You must either link this requirement to other requirements
         using the derived_from attribute, or you need to set
         top_level to true."""
  }
  ```

  Would now produce something like this:

  ```
  Requirement Potato {
              ^^^^^^ checks-5/foo.trlc:3: check error: linkage incorrect
                   | You must either link this requirement to other requirements
                   | using the derived_from attribute, or you need to set
                   | top_level to true.
  ```

  For more details please
  [refer to the LRM](https://bmw-software-engineering.github.io/trlc/lrm-2.9.html#bnf-check_declaration).

### 1.1.9

* [TRLC] Add support for Python 3.11. We now support Python 3.8 up to
  and including 3.11.

* [TRLC] Add new option `--no-detailed-info` which supresses the
  additional information the linter may add to a message, such as
  counter-examples or reasoning.

* [TRLC] The tool is now much less likely to abort on parse errors,
  instead we continue where it's possible to generate more errors in
  other unrelated packages and declarations. This may occasionally
  generate follow-on errors that look weird, however once you fix the
  earlier errors things should work out.

* [TRLC] Add new option `--no-error-recovery` which restores the old
  behaviour w.r.t. error handling. With this option, every error you
  see is absolutely a real error which you need to fix; but of course
  there could be more errors once you fix them.

* [LRM] Mark `.check` files as a deprecated feature. You should move
  your checks into the corresponding `.rsl` file. The linter also
  complains about these now.

### 1.1.8

* [TRLC] Hotfix for the CVC5 API issue: pinning PyVCG to 1.0.3, which
  in turn pins CVC5 to 1.0.5 (the last known good version).

### 1.1.7

* [TRLC, LRM] Fixed a missing restriction on tuple types that
  permitted interesting nesting of tuples with separators and optional
  components. The restriction forbids any tuple with declared
  separators from having components that are themselves tuples with
  separators. We may relax this restriction in the future to permit
  some combinations where this doesn't lead to parsing problems for
  values.

  The problem can be seen in this example:

  ```trlc
  tuple T {
     a String
	 separator @
	 b optional Integer
  }

  tuple Q {
     a T
	 separator @
	 b optional Integer
  }
  ```

  If we now write `"foo" @ 12` then there is no possible way to
  specify if you meant:

  * Instance of Q where `a` is `"foo" @ 12` and `b` is unspecified
  * Instance of Q where `a` is just `"foo"` and `b` is `12`

* [TRLC, LRM] Fixed LRM and tools allowing empty enumerations. This is
  now explicitly forbidden. It was always unreasonable to do this as
  it would have been impossible to use the enumeration type, and there
  is no legitimate use-case anyway since you cannot add more literals
  later through e.g. a type extension.

* [TRLC] Add alternative entry-point for users who cannot modify their
  PATH. You can now do `python3 -m trlc [args...]` and it works just
  like `trlc [args...]`.

* [TRLC] Fix tool crash when encountering a file not in UTF-8
  encoding. We now print an error message indicating the issue.

* [TRLC] Fix bug when parsing arrays: arrays without comma separators
  were accapted when they should have been rejected.

* [TRLC] Fix tool crash when parsing a file with an unterminated `/*`
  comment.

* [LRM] Fix typo in in several places: `.rls` should be `.rsl`.

### 1.1.6

* [TRLC] Add new option `--lint --verify`. This option requires
  [PyVCG](https://pypi.org/project/PyVCG) to be installed (which is
  only available on GNU/Linux or OSX). This option attempts to
  statically verify all checks for freedom of run-time errors (no null
  dereferences, no division by zero, and no array out of bounds
  access). For example with this `.rsl`:

  ```
  type T1 {
    x optional Integer
    y optional Integer
    z          Integer
  }

  checks T1 {
    x != null implies y == x, fatal "potato"
    y != null implies x > 1, warning "potato"
  }
  ```

  The `--lint --verify` option might say:

  ```
  y != null implies x > 1, warning "potato"
                    ^ test1.rsl:11: warning: expression could be null [vcg-evaluation-of-null]
                    | example record_type triggering error:
                    |   T1 bad_potato {
                    |     /* x is null */
                    |     y = 0
                    |     z = 0
                    |   }
  ```

* [Package] Provide Linux and OSX packages, along with the default
  package, which should automatically install PyVCG where it is
  available. On Windows, `pip` should fall back to the platform
  agnostic package.

* [TRLC] Add new option `--no-user-warnings` to suppress any warning
  generated from a user-defined check.

* [TRLC] Fix missing static check on exponents (they must not be
  negative).

* [TRLC] Fix missing static check for Boolean types on check
  expressions (tools would crash without error message).

* [TRLC, LRM] Fix several tool crashes when the `null` literal
  appeared in expressions outside equality. Re-worded the section on
  null values in the LRM to be much stricter. We consider this to be a
  bug-fix and not a change of semantics.

* [LRM] Clarify equality semantics for arrays, tuples, and record
  references. Moved the definition of null equality into the same
  place.

### 1.1.5

* [LRM, TRLC] Remove limitation on late packages. You may now declare
  any number of packages in `trlc` files; and you may even import
  them. It is still recommended to have a `rsl` file for a package
  spanning multiple files, even if it's basically blank; however the
  technical limitation and language rules surrounding late packages
  have been removed.

* [LRM, TRLC] Add base 2 and base 16 integer literals. You can now
  write things like `0xdeadbeef` and `0b10010010`. Octal literals are
  not supported.

* [LRM, TRLC] Add support for readability separators in integer and
  decimal literals. You can now write things like `1_000_000.00` or
  `0b1001_0010`.

* [TRLC] Improve --lint output by appending a rule name in the output
  (in a style similar to clang-tidy). In the future it will be
  possible to turn rules off you don't like.

* [TRLC] Relax errors surrounding array sizes, they are now lint
  messages like the language manual suggests.

* [TRLC] A warning is now issued by the tools when encountering a
  duplicate import statement.

* [TRLC] A warning is now issued by the tools when encountering
  duplicate late package declarations.

* [TRLC] New --lint check for detecting tuples with separators that
  could be confused with base 2 or base 16 integer literals.

### 1.1.4

* [TRLC] Improve error messages by using a more human readable form of
  expected tokens, so now you see "opening brace '{'" instead of
  "C_BRA".

### 1.1.3

* [TRLC] New API function `fully_qualified_name` for `Record_Object`
  which can be used to get the `package.name` name for any record.

* [TRLC] The API function `to_python_object` now emits fully qualified
  names for record references.

### 1.1.2

* [LRM, TRLC] Also allow `:` and `;` as a tuple field separators.

### 1.1.1

* [LRM, TRLC] New (backwards-incompatible) keywords: `tuple`,
  `separator`, `freeze`, `abstract`, and `final`. New punctuation:
  `@`.

* [LRM, TRLC] Support for tuple types: these are algebraic datatypes
  that also support user-defined syntax. The main use case is
  versioned identifiers, e.g. allowing you to write `12345@42` for
  example to refer to a codebeamer item 12345 at version 42. Instead
  of only allowing this use-case, tuples should be a widely applicable
  generic datatype, for specifying e.g. coordinates, qualified
  information, complex numbers, vectors, etc.

  Have a look at the new [Tuples Tutorial](TUTORIAL-TUPLES.md) for
  some examples.

* [LRM, TRLC] Support for freezing record components: you can now
  declare that a particular component is always a certain value for
  all instances of that record type. This is not the same as a
  "default" value, instead that value can never be changed,
  overwritten, or unfrozen again.

  Have a look at the updated [Catch-all base types
  tutorial](TUTORIAL-OPTIONAL-BASE.md) for an example.

* [LRM, TRLC] Support for abstract and final types: abstract must be
  extended before they can be used, and final types cannot gain new
  components.

  Have a look at the new [Advaned tips &
  tricks](TUTORIAL-ADVANCED-TYPES.md) tutorial for examples.

* [TRLC] Introducing the tuple type required significant
  reorganisation of the AST, to mark this significant backwards
  incompatible change we have increased the minor version instead of
  just the patch version. The key incompatible changes are:

  * New base-class for record types and tuple types, called
    `Composite_Type`.

  * Components and fields now share the same type
    `Composite_Component`.

  * New base-class `Typed_Entity` for entities with a type, in which
    case the type is stored in the `n_typ` attribute. The entities
    `Quantified_Variable`, `Composite_Component` (previously
    `Record_Component`), `Enumeration_Literal_Spec`, and
    `Record_Object` are now typed entities, and their inconsistent
    attribute for their type is now `n_typ` consistently.

  * Renamed `n_record` to `n_type` for `Composite_Component` (formally
    `Record_Component`).

* [TRLC] Fix unary operators in array aggregates; this used to crash
  the tools and now works as expected.

* [TRLC] Fix anchoring of some error messages which incorrectly linked
  to the declaration of `x` instead of the part of the expression
  where `x` was used.

* [TRLC] Warning and error messages that show source context now strip
  leading spaces to preserve space.

* [TRLC] User defined types (records, enumerations, and tuples) now
  all subclass from `Concrete_Type` in the API which provides a useful
  new function: `fully_qualified_name()` which returns something like
  `package.typename`. These types are now also python hashable, so you
  can create dictionaries and sets with them without issues.

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
