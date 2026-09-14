# TRLC Tutorial (Packages and Sections)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## Scaling up

TRLC is designed to be used in large organisations and projects. TRLC
offers a three features that can be used to control the
complexity. These features may not be helpful for smaller independent
software projects, but in gigantic projects they can be very helpful:

* Packages (a way of grouping data beyond files)
* Sections (a way of grouping requirements inside files)
* Includes (making trlc parse only some files)

## Packages

Packages are a way to segment and structure the name space.

Each `.rsl` and `.trlc` file must start with a package indication.

This has two effects:

* Things you declare belong to that package
* Things you reference within the package `P` do not need to be
  prefixed with `P.`

For example consider this `.rsl`:

```
package Base

type Requirement {
  description String
  related_to  optional Requirement
}
```

This is a `.rsl` file that our global requirements managers have
provided to us. Everyone uses it.

But when we create requirements for out component then we should
create a new package in my `.trlc` file. To make use of the types from
`Global` we need to import it first:

```
package Car
import Base
import Motorcycle

Base.Requirement wheel_count {
  description = "the number of wheels is four"
  related_to  = Motorcycle.wheel_count
}
```

You can import as many other packages as you want, and you can
reference requirements from other packages (as long as you import them
first). Requirements can have the same name, as long as their package
is different.

Finally not that you can have many `.trlc` files that contribute to
the same package. For example instead of having one massive file
`car.trlc`, you could have many: `engine_control.trlc`,
`cruise_control.trlc`, `radar.trlc`, etc.

## Subpackages

In very large projects a single flat list of package names becomes hard
to manage. Package names may instead be *dotted*, forming a hierarchy of
subpackages:

```
package com.bigcorp.safety
```

Before you can declare a nested package, every prefix must already be a
declared package. So to declare `com.bigcorp.safety` you must also have
declared `com` and `com.bigcorp` somewhere (each in its own `.rsl`
file).

For example, you would need three separate `.rsl` files:

```
// com.rsl
package com
```

```
// com.bigcorp.rsl
package com.bigcorp
```

```
// com.bigcorp.safety.rsl
package com.bigcorp.safety

enum ASIL_Level { QM A B C D }
```

To reference a type or object from a nested package, use its full dotted
prefix:

```
package com.bigcorp.brakes
import com.bigcorp.safety

type Brake_Requirement {
  level com.bigcorp.safety.ASIL_Level
}
```

### Importing subpackages

Importing is *not* transitive: `import com.bigcorp.safety` gives you
access to the types in `com.bigcorp.safety` only — not to its parent
`com.bigcorp`, and not to any of its children.

If you want a whole subtree at once, use a *wildcard import*:

```
package com.bigcorp.brakes
import com.bigcorp.safety.*

type Brake_Requirement {
  level   com.bigcorp.safety.ASIL_Level         // from com.bigcorp.safety
  unit    com.bigcorp.safety.units.Pressure      // from a child package
}
```

`import com.bigcorp.safety.*` makes `com.bigcorp.safety` **and every
package below it** visible. The linter will warn you about a wildcard
import that ends up unused, and about an explicit import that is already
covered by a wildcard.

A small note on the `.` separator: it means different things depending
on what is to its left. After a *package* it descends the namespace
(`com.bigcorp.safety.Type`); after a *value* it accesses a tuple or
record field (`my_record.field`). TRLC resolves the package prefix
first, against the imported packages, before any field access — so there
is no ambiguity. To keep it that way, a subpackage's leaf name must be
distinct from any type or object in its parent package (TRLC rejects the
clash).

## Sections

Even if you split the requirements of your project over many files,
you still might want additional ways of grouping related requirements
together in one file. Sections are one possible way of doing this and
are best illustrated by example:

```
package Potato

section "Non-Functional Requirements" {

  Requirement memory {
    functional  = false
    description = "RAM consumption must be less than 1 MB"
  }

}

section "Functional Requirements" {

  section "Safety-related" {
    Requirement non_exploding {
      functional  = true
      integrity   = ASIL.D
	  description = "the car shall not explode"
	}
  }

  section "Non safety-related" {
    Requirement fuel {
      functional  = true
      integrity   = QM
	  description = "the car shall not use fossil fuels"
	}
    Requirement colour {
      functional  = true
      integrity   = QM
	  description = "the car shall be green"
	}
  }
}
```

These sections have zero impact on the language: name resolution or
referencing is not affected. However this grouping is exposed in the
API so that you could e.g. generate section titles in a PDF rendering
of your requirements.

## Includes

Often when running TRLC you are not really interested in the entire
repository, but only one or two files.

**If** you have sectioned everything nicely with packages (i.e. not
just have one giganting package with 100k requirements) then TRLC
offers an alternative way of running it with the `-I` switch.

For example:

```bash
$ trlc -I global myfile.trlc
```

Would discover trlc files in `global` and analyse their dependencies
and then only pull in the files that are required to understand
`myfile.trlc`. This can massively improve performance, if the
interconnections between the packages are not too dense.
