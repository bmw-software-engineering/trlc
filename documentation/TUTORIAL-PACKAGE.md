# TRLC Tutorial (Packages and Sections)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## Scaling up

TRLC is designed to be used in large organisations and projects. TRLC
offers a two features that can be used to control the
complexity. These features may not be helpful for smaller independent
software projects, but in gigantic projects they can be very helpful.

## Packages

Packages are a way to segment and structure the name space.

Each `.rsl`, `.check` and `.trlc` file must start with a package
indication.

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
	  description = "the car shall not use fossil fuesl"
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
