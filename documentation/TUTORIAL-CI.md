# TRLC Tutorial (Basic Concepts)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## Integrating in CI

TRLC has a special option `--brief` that is designed to integrate the
TRLC tooling into CI. It modifies the output, where normally you'd see
something like this:

```
Requirement fuel {
            ^^^^ car.trlc:13: error: required component critical (see model.rsl:5) is not defined
```

Running in `--brief` mode produces this instead:

```
car.trlc:13:13: trlc error: required component critical (see model.rsl:5) is not defined
```

## Parsing the output

The output is designed to be machine parseable, with the following
regular expression to match:

```
(.*)\.(rsl|trlc|check)(:\d+(:\d+)?)? trlc (lex |check )?(warning|error|ICE): .*
```

The components of this regular expression are:

* filename (with optional line (with optional column))
* message kind, with the following options:
  * trlc lex error (errors during lexing)
  * trlc warning (warnings from the language)
  * trlc error (syntax error)
  * trlc check warning (user defined warnings)
  * trlc check error (user defined errors or fatal errors)
  * trlc ICE (internal compiler errors)
* message

## Enabling extra checks

The TRLC tools also come with a separate `--lint` mode that performs
additional checks. This mode only considers `.rsl` (and `.check`) files,
and in a CI environment this should be run first. A full CI
integration should do the following:

* `trlc --brief --lint` to find any issues in model and checks
* If lint completes successfully, follow up with `trlc --brief` to
  process `.trlc` files and find issues in requirements and execute
  user defined checks

TRLC lint goes beyond what the language definition requires and
produces additional messages that may be helpful. For example it warns
you about deprecated language features:

```
   len == trlc:len(str), warning "potato", len
          ^^^^^^^^ legacy.rsl:9: warning: deprecated feature, please use function len instead
Verified 1 model(s) and check(s) and found 1 warning(s)
```

Using TRLC lint is optional, but highly recommended.

## Return code

The TRLC tool returns 0 if there are no errors (there could be user or
language warnings however).

A status code of 1 is returned in all other cases.
