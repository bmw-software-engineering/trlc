# TRLC Tutorial (Basic Concepts)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## Basic concepts

The intended domain of TRLC is writing requirements in the context of
large (possibly safety critical) software projects. In large
organisations you have a lot of requirements, a lot of links,
different levels and a ton of meta-data.

In TRLC there are currently three kinds of files, split into two
areas. For the requirements managers:

* `.rsl` files that define the global structure (e.g. what is a requirement)
* `.check` files that define constraints (e.g. when is a requirement
  well-formed)

And for the software developers:

* `.trlc` files that define actual requirements

This split is maybe not interesting for small projects, but for large
organisations (like BMW) it is quite helpful.

## First example

Let's get started with a really easy example. In the `model.rsl` we write:

```
package Example

type Requirement {
  description String
  critical    Boolean
}
```

Here we define a `Requirement` type that we'll later use to write our
requirements. It has two attributes: the `description` where we'll
write the requirement text and a flag `critical` to indicate if this
is safety-related or not.

Don't worry about the `package Exampele` yet, this is explained much
later in the [Packages](TUTORIAL-PACKAGE.md) tutorial.

Attributes have types, and the TRLC language provide a bunch of basic
built-in types: `Boolean`, `Integer`, `Decimal`, `String` and
[`Markup_String`](TUTORIAL-ADVANCED.md); and a way to create
user-defined enumeration types.

We can then start to define requirements for our software project in a
`car.trlc` file:

```
package Example

Requirement shape {
  description = "Our car shall have four wheels."
  critical    = false
}

Requirement safety {
  description = "Our car shall not explode."
  critical    = true
}
```
Here we've written two requirements, `shape` and `safety` using
the `Requirement` type we've been given.

## Adding documentation

There are two ways you can add documentation to TRLC. There are
comments and descriptions. Comments can be placed anywhere and they
are completely ignored by the tools:

```
// This is the main requirements type
type Requirement {
  description String
  critical    Boolean
}
```

Descriptions are optional text strings that can be placed after some
names. They do not have any semantic impact on anything, but they are
exposed by the API.

```
type Requirement {
  description "Main body of the requirement"
    String

  critical "If true, then this is a safety related requirement"
    Boolean
}
```

In Python terms, they are very similar to a docstring. Not doing
anything when running the program, but used by other tools e.g. pydoc.

## Using the tools

The TRLC tools are useful to check if the requiremens are well
formed. So far they are, but lets add another requirement:

```
Requirement fuel {
  description = "The car shall not use any fossil fuels."
}
```

If we run the tools, we will find out there is a problem:

```
$ trlc requirements_dir
Requirement fuel {
            ^^^^ car.trlc:13: error: required component critical (see model.rsl:5) is not defined
```

In this case the problem is that the required field critical has not
been provided.

## Optional attributes

One way to fix this, is of course to add the missing attribute. But
that may not be reasonable or desired in all cases, and so TRLC allows
you to make an attribute optional. We can change the model like this:

```
type Requirement {
  description          String
  critical    optional Boolean
}
```

## No defaults, only freezing

It is tempting at this point to want a way to specify the "default"
for attributes, but this is not supported by design. There are two
reasons for this:

* It is important for requirements to be always readable from just
  looking at the `.trlc` file.
* In a safety-critical context, if the default ever changes it would
  create a very tricky situation when it comes to software
  traceability.

However, there is a way to permanently nail down a value using
`freeze`:

```
type Critical_Requirement extends Requirement {
  freeze critical = true
}
```

Note that this is _not_ a default: it is permenently set in stone. If
you ever attempt to set `critical` in a `Critical_Requirement` then
you will get an error.
