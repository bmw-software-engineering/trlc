# TRLC Tutorial (Using the linter)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## Using the linter

The TRLC tools come with a static analysis tool that can diagnose some
potential issues with `.rsl` and `.check` files before they are
deployed and used.

To do this simply use the `--lint` feature:

```bash
$ trlc --lint DIRECTORIES_OR_FILES
```
To enable more detailed checks you can also use the `--lint --verify`
feature, but please note that this is only available on Linux and OSX,
and requires you to have installed the optional dependency
[PyVCG](https://pypi.org/project/PyVCG).

```bash
$ trlc --lint --verify DIRECTORIES_OR_FILES
```

## Sanity checks

The linter can detect some questionable constructs, for example:

```
tuple T {
  a Integer
  separator x
            ^ lint-ambiguous-literals/foo.rsl:5: warning: x
			    separator after integer component creates
				ambiguities with base 16 literals
				[separator_based_literal_ambiguity]
  b optional Integer
}
```

In this example there is a possible problem with the tuple literal `0
x 12` and the integer hex literal `0x12`. Even worse `0x12` is a valid
instance of the tuple here (with a = 18), but `0 x 12` is a different
instance (with a = 0, and b = 12).

## Verification

The TRLC expression language can create run-time errors in some
contexts:

* evaluation of null in any context other than equality
* division by zero
* array out of bounds

The `--lint --verify` feature can also find cases where the check
could be improved to guard against such as problem. For example:

```trlc
type T {
  x optional Integer
}

checks T {
  x > 0, "please make this positive", x
}
```

When running the verifier we can see:

```plain
$ trlc.py --lint --verify trivial.rsl
x > 0, "please make this positive", x
^ trivial.rsl:8: warning: expression could be null [vcg-evaluation-of-null]
| example record_type triggering error:
|   T bad_potato {
|     /* x is null */
|   }
Verified 1 model(s) and 0 check(s) and found 1 warning(s)
```

And indeed, if we create a requirement as shown in the example then
the tools would fail:

```plain
$ trlc.py trivial.rsl trivial.trlc
T bad_potato {
  ^^^^^^^^^^ trivial.trlc:3: error: lhs of check x > 0 (trivial.rsl:8) must not be null
```

We should now look at the counter-example and think about how we can
improve our check. In most cases we just need to guard against the
null evaluation:

```trlc
checks T {
  x != null implies x > 0, "please make this positive", x
}
```

When running the verifier now we no longer get a complaint:

```plain
$ trlc.py --lint --verify trivial.rsl
Verified 1 model(s) and 0 check(s) and found no issues
```

### Caveat

Please keep in mind two limitations with the `--lint --verify`
feature:

* It currently does not work on Windows
* Under some circumstances the counter-examples generated are
  impossible to achieve, due to how the underlying technology (SMT
  Solvers) works. The current limitations are documented in the
  [release note](CHANGELOG.md).
