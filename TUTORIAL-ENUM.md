# TRLC Tutorial (Enumerations)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## Enumerations

Creating user-defined enumerations is easy:

```
enum ASIL {
   QM "not safety releated"
   A
   B
   C
   D
}
```

Like with records, you can add description strings to none, some, or
all of the members.

Enumerations members have to be unique for the enumeration they belong
to, but it is possible to have the same name elsewhere:

```
enum Language {
   Ada
   C    // Does not conflict with ASIL.C
   Rust
}
```

## Using enumerations

These new types can be used in records:

```
type Requirement {
   description String
   integrity   ASIL
}
```

And when writing requirements you assign enumerations qualified by
with the enumeration name:

```
Requirement potato {
   description = "Potato"
   integrity   = ASIL.QM
}
```
