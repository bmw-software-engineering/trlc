# TRLC Release Notes

## Language support

Up to date with version 2.2 of TRLC language reference manual.

## Limitations

None.

## Changelog


### 1.0.6-dev

* [LRM, TRLC] Support declarations of checks in the `.rsl` files. This
  means you don't need to have a separate check file, allowing you to
  implement your process or business logic closer to the type
  declarations. Dedicated check files continue to be supported.

* [LRM, TRLC] Rework builtin functions to not have the ugly `trlc:`
  prefix. Builtin functions now look more natural, e.g. `len` instead
  of `trlc:len`. The legacy functions will remain as a deprecated
  feature, and we'll remove them at a future date.

* [TRLC] Fix bug in array parsing and evaluation.

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
