# TRLC Tutorial (Catch-all base types)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## The problem

To make everyone be able to link their requirements to other items, it
is implicitly encouraged to provide a very generic base type that
everyone uses. For example:

```
enum ASIL { QM A B C D }

enum COMPONENT {
  Engine
  Brakes
  Cruise_Control
}

type Requirement {
  description optional String
  component   optional COMPONENT
  picture     optional String
  asil        optional ASIL
  derived     optional Requirement [0 .. *]
  cb_link     optional Integer
}
```

There is a lot of `optional` here. This doesn't really matter except
when you start to write checks. Lets say we want to make sure that all
Engine requirements have an asil level equal to D, and a
description. The obvious thing does not work:

```
checks Requirement {
  component == COMPONENT.Engine implies
    (asil == ASIL.D and
	 len(description) > 0),
  error "set description and asil"
}
```

The reason this does not work is that you need to guard against `null`
in all these, so the check should be:

```
checks Requirement {
  component != null and component == Engine implies
    (asil != null and
	 description != null and
	 asil == ASIL.D and
	 len(description) > 0),
  error "set description and asil"
}
```

This is not only error prone, but it is also quite hard to
understand. (Although the [--verify feature](TUTORIAL-CI.md) of TRLC
can find any issue in such an expression.)

## Solution 1: refactor types and freeze components

One way to fix this problem is to have fewer attributes and fewer
optional attributes in your types, and freeze components that never
change. You could, for example, rework the above example like so:

```
type Requirement {
  description optional String
  asil                 ASIL
}

type Component_Requirement extends Requirement {
  component COMPONENT
}

type Engine_Requirement extends Requirement {
  freeze component = COMPONENT.Engine
}

checks Engine_Requirement {
  asil == ASIL.C or asil == ASIL.D,
    "Engine req should be ASIL C or D"

  description != null and len(description) > 0,
    "Must have a description"
}
```

This is great _if you can do it_, but if you have other requirements
with e.g. an ASIL level then you don't want to introduce the same
component in more than one subtype.

## Solution 2: empty and frozen extensions

Another way to deal with this problem is to create empty extensions
with additional fatal checks. This allows you to keep the very generic
base type:

```
type Requirement {
  description optional String
  component   optional COMPONENT
  picture     optional String
  asil        optional ASIL
  derived     optional Requirement [0 .. *]
  cb_link     optional Integer
}

type Engine_Requirement extends Requirement {
  freeze component = COMPONENT.Engine
  freeze asil      = ASIL.D
}

checks Engine_Requirement {
  description /= null, fatal "description must be set"

  len(description) > 0, "empty description not allowed"
}
```

The first check must be `fatal` in order to prevent the other
check being evaluated with potential `null` values.

This is way more readable than the original convoluted expression, and
allows you to build a type hierarchy on top. For example you could
have safety requirements that needs an ASIL level set, and you can
base your engine requirement on that.

Empty type extensions can be very helpful to simplify writing complex
checks.
