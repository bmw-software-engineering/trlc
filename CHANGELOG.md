# TRLC Release Notes

## Language support

Up to date with version 2.8 of [TRLC language reference
manual](https://bmw-software-engineering.github.io/trlc/lrm.html).

## Limitations

The new `Markup_String` type currently has limited language support,
but we expect to add more features surrounding it later. (For example
quantifying over all references.)

The `--verify` feature has several limitations:

* Decimal numbers are modelled as real numbers instead of
  decimals. This means there may be false alarms and counter-examples
  produced that do not make sense.
* Quantifiers are supported, however there may be false alarms and
  incorrect counter-examples generated. Especially for nested and
  nested alternating quantifiers.
* Tuples in arrays currently not get their constraints asserted,
  leading to false alarms and invalid counter-examples.
* Markup_Strings are treated just like strings (i.e. they do not carry
  a constraint yet about legal syntax of inline references).
* It does not support frozen components.
* It does not support the builtin `matches` function.
* It does not support field access (the `.` operator).
* Issues with checks on record extensions are reported multiple times
  (once for each extension).

## Changelog

### 1.1.6-dev

* [TRLC] Add new option `--no-user-warnings` to supress any warning
  generated from a user-defined check.

* [TRLC] Fix missing static check on exponents (they must not be
  negative).

* [TRLC, LRM] Fix several tool crashes when the `null` literal
  appeared in expressions outside equality. Re-worded the section on
  null values in the LRM to be much stricter. We consider this to be a
  bug-fix and not a change of semantics.

* [LRM] Clarify equality semantics for arrays, tuples, and record
  refereences. Moved the definition of null equality into the same
  place.

* [TRLC] Add new *experimental* option `--lint --verify`. This option
  requires [PyVCG](https://pypi.org/project/PyVCG) to be installed
  (which is only available on GNU/Linux or MacOS). This option
  attempts to statically verify all checks for error freedom (no null
  dereferences, and no division by zero). For example with this `.rsl`:

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
                    ^ test1.rsl:11: check: expression could be null
                    | example record_type triggering error:
                    |   T1 bad_potato {
                    |     /* x is null */
                    |     y = 0
                    |     z = 0
                    |   }
  ```


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
