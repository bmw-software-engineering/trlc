# TRLC Tutorial (Using the linter)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## Using the linter

The TRLC tools come with a [static analysis tool](linter.md) that can
diagnose some potential issues with `.rsl` files before they are
deployed and used. This is enabled by default, but you can turn these
off with the `--no-lint` option.

To enable more detailed checks you can also use the `--verify`
feature, but please note that this is only available on Linux, and
requires you to have installed the optional dependency
[CVC5](https://pypi.org/project/cvc5).

```bash
$ trlc --verify DIRECTORIES_OR_FILES
```

If you are on Windows or Linux, you can also download the CVC5
executables and ask TRLC to use them directly:

```bash
$ trlc --verify --use-cvc5-binary=path/to/cvc5.exe DIRECTORIES_OR_FILES
```

## Sanity checks

The linter can detect some questionable constructs, for example:

```
tuple T {
  a Integer
  separator x
            ^ ./foo.rsl:5: warning: x separator after integer
              component creates ambiguities
              [separator_based_literal_ambiguity]
            | For example 0x100 would be a base 16 literal
            | instead of the tuple segment 0 x 100.
  b optional Integer
}
```

For some more difficult to understand problems (as seen above) a more
detailed description with examples is attached.

## Verification

The TRLC expression language can create run-time errors in some
contexts:

* evaluation of null in any context other than equality
* division by zero
* array out of bounds

The `--verify` feature can also find cases where the check
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
$ trlc.py --verify trivial.rsl
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
$ trlc.py --verify trivial.rsl
Verified 1 model(s) and 0 check(s) and found no issues
```

### Caveat

Please keep in mind two limitations with the `--verify`
feature:

* It is harder to use and much slower on Windows
* Under some circumstances the counter-examples generated are
  impossible to achieve, due to how the underlying technology (SMT
  Solvers) works. The current limitations are documented in the
  [release note](CHANGELOG.md).
