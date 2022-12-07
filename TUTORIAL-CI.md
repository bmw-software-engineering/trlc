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

## Return code

The TRLC tool returns 0 if there are no errors (there could be user or
language warnings however).

A status code of 1 is returned in all other cases.
