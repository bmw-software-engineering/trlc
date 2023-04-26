# TRLC Tutorial (Tuples)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## Tuples

TRLC allows you to create used-defined algebraic datatypes, generally
referred to as "tuples". For example:

```
type Coordinate {
   x Decimal
   y Decimal
}

type Requirement {
   description String
   coordinate  Coordinate
}
```

This allows us to specify inline bundled data in a convenient way. You
can now write:

```
Requirement potato {
   description = "draw something here"
   coordinate  = (42.0, 0.666)
}
```

Tuples can contain any kind of data, including other tuples; but it is
not possible to have array fields or create recursive tuples.

## Syntactic sugar

There is one additional form for tuples that can be used to allow
convenient inline writing of simpler tuples. Consider a pairing of an
item plus its version:

```
tuple Codebeamer_Id {
   item    Integer
   separator @
   version optional Integer
}
```

When using this syntax, then tuple instances you write can be much
shorter, for example:

```
   derived_from_codebeamer = [ 12345,
                               555@42 ]
```

Both of these are instances of `Codebeamer_Id`, the first one is has
version set to `null`, and the second one has version set to `42`.

There two important rules:

* Only tuples with `separator` may have optional fields

* Once a field is optional, all following fields must also be optional

## Writing checks

You can also write checks for tuples, just like you can for record
types. For example:

```
checks Codebeamer_Id {
   item >= 1,
     error "CB Item must be positive", item

   version != null implies version >= 1,
     error "CB Version must be positive", version
}
```

In other checks you can access tuple fields using the `.` notation:

```
checks Requirement {
   (forall cb_item in derived_from_cb =>
      cb_item.item >= 50000),
   warning "this item is suspiciously low"
}
```
