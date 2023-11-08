# User guide: TRLC static analyser and linter

## Purpose

The TRLC static analyser and linter can be used to find misleading or
problematic types and user defined checks. It is recommended to use
it.

## Usage

The linter is enabled by default, so running `trlc filename.rsl` will
also run the linter. The static analyser can be enabled with the
`--verify` option, i.e: `trlc --verify filename.rsl`.

You can explicitly turn the linter off with the `--no-lint` option.

## Checks

### Linter checks

#### clarify_final

Final is a type attribute that is inherited. However for readability
it is a good idea to explicitly state it again.

```trlc
package Clarify_Final

final type T {
  x Integer
}

type Q extends T {
}
```

Generates this message:

```plain
type Q extends T {
     ^ clarify_final.rsl:7: issue: consider clarifying that this record is final [clarify_final]
     | Parent record Clarify_Final.T is final, making this record
     | also final. Marking it explicitly as final
     | clarifies this to casual readers.
```

#### unary_minus_precedence

A curiosity of the TRLC expression grammar (which strongly derives
from the Ada grammar, which shares this particularity) is that unary
minus followed by a stronger binding operator doesn't have the
precedence you think it does. For example:

```trlc
package Unary_Minus_Precedence

type T {
  x Integer
}

checks T {
  -x / 3 < 0, "non-obvious meaning"

  (-x) / 3 < 0, "clear meaning"

  -(x / 3) < 0, "clear meaning"
}
```

Will generate the following message:

```plain
-x / 3 < 0, "non-obvious meaning"
^ unary_minus_precedence.rsl:8: issue: expression means -(x / 3), place explicit brackets to clarify intent [unary_minus_precedence]
```

#### abstract_leaf_types

Abstract types that are never extended can't be used. Most likely they
are remnants of some refactoring.

```trlc
package Abstract_Leaf_Types

abstract type T {
  description String
}
```

Will generate:

```plain
abstract type T {
              ^ abstract_leaf_types.rsl:3: issue: abstract type T does not have any extensions [abstract_leaf_types]
```

#### deprecated_feature

Some features in TRLC are deprecated, that are scheduled to be removed
for version 2.0.0. The linter can notify you when you're using such a
construct, and how it should be done in the future. Right now these
two features are:

* `.check` files (just move the check blocks into the `.rsl` file)
* The legacy `trlc:len` style of builtin functions (just use
  e.g. `len` instead)

#### separator_based_literal_ambiguity

Tuple types with their custom separators offer a lot of potential for
convenient syntax. There is however a specific combination that is
problematic:

```trlc
package Separator_Based_Literal_Ambiguity

tuple T {
  value_1 Integer
  separator x
  value_2 optional Integer
}

type Q {
  value T
}
```

Consider possible assignments to `value`:
* `0` (tuple where value_1 = integer 0)
* `0x0` (tuple where value_1 = hex integer 0x0, but value_2 is null)
* `0 x 0` (tuple where value_1 = integer 0, and value_2 is integer 0)

This is only the case of literal separators `x` and `b`, and only when
they follow an integer or decimal type. The linter generates a message
in this case:

```plain
separator x
          ^ separator_based_literal_ambiguity.rsl:5: issue: x separator after integer component creates ambiguities [separator_based_literal_ambiguity]
          | For example 0x100 would be a base 16 literal
          | instead of the tuple segment 0 x 100.
```

#### impossible_array_types

Some arrays bounds produce arrays that could never be written. For
example:

```trlc
package Impossible_Array_Types

type T {
  x Integer [10 .. 3]
  y Integer [0 .. 0]
}
```

This generates:

```plain
x Integer [10 .. 3]
                 ^ impossible_array_types.rsl:4: issue: upper bound must be at least 10 [impossible_array_types]
y Integer [0 .. 0]
                ^ impossible_array_types.rsl:5: issue: this array makes no sense [impossible_array_types]
```

#### weird_array_types

Related to the check above, you could create arrays that shouldn't be
arrays.

```trlc
package Weird_Array_Types

type T {
  x Integer [1 .. 1]
  y Integer [0 .. 1]
}
```

Would produce the following messages:

```plain
x Integer [1 .. 1]
                ^ weird_array_types.rsl:4: issue: array of fixed size 1 should not be an array [weird_array_types]
                | An array with a fixed size of 1 should not
                | be an array at all.
y Integer [0 .. 1]
                ^ weird_array_types.rsl:5: issue: consider making this array an optional Integer [weird_array_types]
                | An array with 0 to 1 components should just
                | be an optional Integer instead.
```

### TRLC static analyser checks

#### vcg-evaluation-of-null

Evaluating null in any context other than equality is an error. For
example:

```trlc
package Evaluation_Of_Null

type Requirement {
  description optional String
}

checks Requirement {
  len(description) >= 10, "too short"
}
```

Would generate:

```plain
len(description) >= 10, "too short"
    ^^^^^^^^^^^ evaluation_of_null.rsl:8: issue: expression could be null [vcg-evaluation-of-null]
              | example record_type triggering error:
              |   Requirement bad_potato {
              |     /* description is null */
              |   }
```

To fix this you should prefix the check with a guard, for example like
this:

```trlc
checks Requirement {
  description != null implies len(description) >= 10, "too short"
}
```

#### vcg-div-by-zero

Dividing by zero is always bad. For example:

```trlc
package Div_By_Zero

type T {
  x Integer
  y Integer
}

checks T {
  x > 2, fatal "x too small"
  y > 2, fatal "y too small"

  100 / (111 - x * y) > 0, "example"
}
```

Would generate:

```plain
100 / (111 - x * y) > 0, "example"
    ^ div_by_zero.rsl:12: issue: divisor could be 0 [vcg-div-by-zero]
    | example record_type triggering error:
    |   T bad_potato {
    |     x = 3
    |     y = 37
    |   }
```

To fix this either don't do such weird things ;) or perhaps use a
prime number instead of 111:

```trlc
checks T {
  x > 2, fatal "x too small"
  y > 2, fatal "y too small"

  100 / (113 - x * y) > 0, "example"
}
```

With that fix the static analyser doesn't complain anymore as there is
no way to get 113 by multiplying two numbers greater than 2.

#### vcg-array-index

Going out of bounds is also a classic error:

```trlc
package Array_Index

type T {
  x Integer [1 .. 10]
}

checks T {
  len(x) >= 0 implies x[3] > 0, "too small"
}
```

Would generate:

```plain
len(x) >= 3 implies x[3] > 0, "too small"
                     ^ array_index.rsl:8: issue: array index could be larger than len(x) [vcg-array-index]
                     | example record_type triggering error:
                     |   T bad_potato {
                     |     x = [1, 1, 1]
                     |   }
```

You could fix this by either remembering that arrays start at 0 (so
change to `len(x) >= 4`) or perhaps by making sure the array is always
at least 4 elements long (i.e. `x Integer [4 .. 10]`).

#### vcg-always-true

Sometimes checks are just tautologies, and so they don't really serve
any purpose.

```trlc
package Always_True

type T {
  description optional String
}

type Q extends T {
  freeze description = "potato"
}

checks Q {
  description != null, "description cannot be empty"
}
```

Would generate predictably:

```plain
description != null, "description cannot be empty"
            ^^ always_true.rsl:12: issue: expression is always true [vcg-always-true]
```

Maybe you meant to attach this check to type T instead of Q? I.e. like so:

```trlc
package Always_True_Fixed

type T {
  description optional String
}

checks T {
  description != null, "description cannot be empty"
}

type Q extends T {
  freeze description = "potato"
}
```

The static analyser does not consider this check to be always true
now, since you could have instances of just T, even though Q would
always make it true.
