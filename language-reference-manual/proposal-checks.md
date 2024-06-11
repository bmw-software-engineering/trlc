# New checks

The existing checks have several issues:

* They are syntactically detached from the type.
* There is unspecified behaviour in the LRM if there is more than one
  check declared.
* Larger checks with recurring preconditions are tedious to
  write. While it may be possible to subtype some of these, it's not
  always possible or desired.
* Sometimes an expression needs to be reused and this is also tedious

```trlc

type T {

  a Integer
  b Integer
  c String
  d Integer [1 .. *]

  begin checks

    if a > b then
       assert c == "gt", "blah"
    elif a < b then
       assert c == "lt", "blah"
    else
       assert c == "eq", "blah"
    end if

    let tmp = a + b

    forall item in d loop
       assert d >= tmp, "blah"
    end loop

  end checks

}
```

Limitations and restrictions:

* The check block has to be the last element of a type declaration
* Only one (per extension)
* Loops are hiding quantifiers and to keep it sane only iterate over
  elements, not indices
* Semantically requivalent to the current checks (no real control
  flow)

Some other consequences and notes:

* Types with a check section cannot have check blocks
* We deprecate check blocks in general
