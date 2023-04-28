# TRLC Tutorial (Advanced types tips and tricks)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## Type Qualifiers

There are two modifiers available when declaring types: `abstract` and
`final`. These may be useful for larger organisations where you have a
more central requirement team and many users of these centrally
defined types.

### Abstract Types

A type marked `abstract` must be extended before it can be used. For
example:

```
abstract type Base_Requirement {
   description optional String
}

type Requirement extends Base_Requirement {
   derived_from Base_Requirement [1 .. *]
}

type Top_Level_Requirement extends Base_Requirement {
}
```

In this example you can create objects of type `Requirement` or
`Top_Level_Requirement`, but you cannot create instances of
`Base_Requirement`.

### Final Types

A type marked `final` cannot be extended with new components. However
users are still allowed to extend it with new checks or freeze any
components they like.

Building on the above example:

```
final type Supplier_Requirement extends Requirement {
   supplier_name String
}

type ACME_Requirement extends Supplier_Requirement {
   freeze supplier_name = "ACME Corporation, Inc."
}
```

This makes sure that any and all supplier requirements are completely
uniform, and nobody adds new fields that may be confusing or
unexpected to the suppliers.
