# TRLC Tutorial (Arrays)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## Arrays

TRLC allows you to specify "one or more" values for any record member.

```
type Requirement {
   description String
   tags        String [1 .. *]
}
```

Here we have a field `tags` that takes one or more strings. Arrays
must have a lower (at least 0) and an upper bound (which can be
unbounded, indicated by a `*`).

When declaring objects you can assign to an array like this:

```
Requirement potato {
   description = "I like potato"
   tags        = ["security-related",
                  "safety-related",
				  "vegetable-related"]
}
```

If you specify too many or not enough elements, you will get errors.

## Notes

Arrays can be `optional` like any other record field.

Note that an optional arrays that is not specified is not the same as
an array with zero elements.

There is (currently) no way of creating 2+ dimensional arrays. If you
think this is important please create a ticket asking for it.
