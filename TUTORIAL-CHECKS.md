# TRLC Tutorial (Checks)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## Checks

Lets say we have a requirement type like this:

```
package Example

enum ASIL {
  QM
  A
  B
  C
  D
}

type Requirement {
  description  String
  functional   Boolean
  integrity    optional ASIL
}
```

In this example, lets say our process says that functional requirement
should have the integrity level set, but non-functional requirements
don't need one.

We could solve this through type extension, but there is an
alternative way to deal with this issue. You can create additional
rules on what is permitted by creating a `.check` file next to the
`.rsl` files:

```
package Example

checks Requirement {
  functional implies integrity != null,
    error "a functional requirement requires an integrity"
}
```

There are two parts here: there is a (Boolean) expression that must be
true, and there is a message to be emitted if the expression is not
true. Here we create an `error`, but you can also create a `warning`
or a `fatal` error:

* When a `warning` is emitted, the tools still continue as is. If only
  warnings were produced the final return code of the TRLC tooling is
  `0`.

* When an `error` is emitted, the tools still continue as is. However
  the final return code of the TRLC tooling is `1`.

* When a `fatal` error is emitted, then the tools stop processing the
  record and continue to the next one (i.e. no more checks are
  evaluated for this object). Fatal errors are useful if you build
  complex checks that build on each other.

And so, when we attempt to write a requirement that violates this, we
get a message:

```
package Example

Requirement foo {
  description = "potato"
  functional  = true
}
```

The tools say:

```
Requirement foo {
            ^^^ example.trlc:3: check error: a functional requirement requires an integrity
```

## Anchoring checks

For better error messages, you can also specify a record component
where the message is attached. For example:

```
package Example

checks Requirement {
  functional implies integrity != null,
    error "a functional requirement requires an integrity"

  integrity == ASIL.D implies trlc:len(description) > 10,
    warning "this is not very descriptive",
    description  // this anchors the check
}
```

Here we've added another check (you can have as many as you want for
any given type) that enforces a minimum length for the description if
the integrity level is ASIL-D.

Normally the message is attached to the declaration like so:

```
Requirement foo {
            ^^^ example.trlc:3: check warning: this is not very descriptive
```
However with the additional record component we've provided to the
check the message now looks like this:

```
  description = "potato"
                ^^^^^^^^ example.trlc:4: check warning: this is not very descriptive
```

## Builtin functions

As seen in the above example, there are some built-in functions that
you can use. They are:

* `trlc:len` can be used to get the length of a string or array
* `trlc:startswith` can be used to test the beginning of a string
* `trlc:endswith` can be used to test the end of a string
* `trlc:matches` tests if a regular expression matches a string

For example:

```
checks Requirement {
   trlc:endswith(description, "."),
     warning "description should end in a full-stop",
	 description

   not trlc:matches(description, "[Ff]ight club"),
     error "we do not talk about fight club",
	 description
}
```

## Boolean expressions

There all the usual connectives are supported, and one that is a bit
more unusual.

* A `and` B
* A `or` B
* A `xor` B
* A `implies` B
* `not` A

The `implies` connective can be used to write conditional checks. You
can read it as "if A then B".

## Arithmetic expressions

The check language also supports integer arithmetic, comparisons and
expressions. For example you can write:

```
A ** 2 + B ** 2 == C ** 2
```

For a full reference, please see the relevant section in the [language
reference manual](language-reference-manual/LRM.md#expressions).

## Null

Optional components are `null`. Null is a special value that can be
tested for, e.g. `foo != null`, but that is pretty much it.

If a `null` value finds its way into e.g. an arithmetic expression
then you get an error.

## Quantifiers

Usually, when you have an array you might want to say something that
should be true for all elements. You can use a quantified expression
for this:

```
checks Requirement {
  (forall tag in tags => not trlc:startswith(tag, "#")),
    warning "please don't use hashtags"
}
```

## Current limitations and notes

Right now it is not possible to "follow references" in the check
language. We are considering to add this in a future release.
