# TRLC Tutorial (References and Extensions)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## References

It is often important to link requirements to each other. TRLC allows
you to do this as well:

```
type Requirement {
  description           String
  derived_from optional Requirement
}
```

When declaring a requirement you can then mention another requirement
by name:

```
Requirement top_level {
   description = "This is my top-level system requirement"
}

Requirement potato {
   description  = "This is a software requirement"
   derived_from = top_level
}
```

## Making use of types

In the above example, there is no real way of telling what a top-level
requirement is, other than context. You could improve the situation
like this:

```
type System_Requirement {
  description String
}

type Requirement {
  description  String
  derived_from System_Requirement
}
```

There are several advantages here:

* You can immediately tell what a top-level requirement is.
* The `derived_from` link is no longer optional. Previously a
  requirement with a null `derived_from` link could either be a
  top-level requirement, or a mistake.

However it is annoying that we had to copy a portion of the
requirement type. Here it is not so bad, but if there is many more
attributes then this duplicate maintenance is a recipe for disaster.

## Extending types

TRLC allows you to avoid this maintenance issues through type
extensions:

```
type Base_Requirement {
  description String
}

type System_Requirement extends Base_Requirement {
}

type Requirement extends Base_Requirement {
  derived_from System_Requirement
}
```

This is the same as above, but if we want to add e.g. an integrity
level to all these requirements then we only have to update
`Base_Requirement` instead of duplicating the change.

Another advantage is that if a reference asks for a
`Base_Requirement`, then it is possible to specify either a
`Requirement` or a `System_Requirement`. With the previous solution of
copying the type this was not possible.

## Additional rules

Type extensions can only be used to add fields. There is no way of
removing a field.

In TRLC most things need to be declared before they can be
used. Record references are an exception to this, you can reference a
requirement that is written later in the file (or even a different
file). This allows you to have circular links if you want. Of course,
it does need to resolve eventually, and the tooling will emit an error
if it is not the case.

Finally note that a reference is always a reference. You cannot
specify an entirely new record "inline". We plan to support something
like this in a future release, but it will be distinct from records.

## In-line references

It is also possible to refer to other TRLC records directly in
text. For this you need to use the `Markup_String` type instead of
`String`.

```
type Requirement {
  description           Markup_String
  derived_from optional Requirement
}

type Constant {
  value Integer
}
```

You can then name any other TRLC record inside a comma-separated list
enclosed in `[[` and `]]`.

```
Requirement potato {
   description  = '''
      The car shall have [[wheel_count]] wheels. Related information
	  can be found in [[Definition.Wheel, Definition.Car]].
   '''
}

Constant wheel_count {
   value = 3
}
```

The advantage of using `Markup_String` is that such references are
checked like any other.
