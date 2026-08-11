# TRLC Formatter — Formatting Rules

This document defines the formatting rules applied by the TRLC Prettier plugin
to `.trlc` (requirements) and `.rsl` (metamodel) files.

---

## Common Rules (apply to both `.trlc` and `.rsl`)

---

### R01 — Indentation: 4 spaces (or tabs)

**Rule:** Use 4 spaces for each level of indentation by default.

Controlled by Prettier's standard `tabWidth` (default `4`) and `useTabs` (default
`false`) options. Set `useTabs: true` to use tab characters instead of spaces.

**Rationale:** Consistent indentation makes block nesting visually clear and
avoids editor/tab-width inconsistencies across teams and tools.

```
// Before
abstract type Requirement {
    description			String   // mixed tabs and spaces
	note optional           String   // tab indent
}

// After
abstract type Requirement {
    description String
    note optional String
}
```

---

### R02 — Trailing whitespace removed

**Rule:** No trailing spaces or tabs at the end of any line.

**Rationale:** Trailing whitespace causes noisy diffs in version control and
serves no purpose.

```
// Before
  description String   ← trailing spaces here

// After
  description String
```

---

### R03 — Single blank line between top-level declarations

**Rule:** Exactly one blank line between top-level declarations (`enum`, `type`,
`abstract type`, `tuple`, `checks`, `section`, record objects).

**Rationale:** Improves readability by visually separating independent
declarations without wasting vertical space.

```
// Before
enum Asil {
  QM
}
enum Status {      // no blank line between
  valid
}

// After
enum Asil {
  QM
}

enum Status {      // one blank line
  valid
}
```

---

### R04 — Single blank line after `package` and `import` block

**Rule:** One blank line after the `package` declaration. One blank line after
the last `import` declaration.

**Rationale:** Clearly separates the file header from the content body.

```
// Before
package ReqSpec
import other_pkg
enum Asil {

// After
package ReqSpec

import other_pkg

enum Asil {
```

---

### R05 — One `import` per line, sorted alphabetically, no blank lines between

**Rule:** Each `import` statement is on its own line. Consecutive `import`
statements are sorted alphabetically (case-insensitive). No blank lines between
consecutive `import` statements.

**Rationale:** Alphabetical ordering makes it easy to find a specific import at
a glance and avoids merge conflicts caused by personal ordering preferences.
Blank lines between imports add unnecessary vertical space.

```
// Before
import ReqSpec

import processes

import Roles

// After
import processes
import Roles
import ReqSpec
```

Controlled by option `trlcSortImports` (default `true`). Set to `false` to
preserve source order.

---

### R06 — Opening brace `{` on same line as declaration

**Rule:** The opening brace `{` must always appear on the same line as its
declaration keyword, never on a new line.

**Rationale:** Consistent brace style (K&R style) reduces visual noise and
prevents the `{` from being separated from its context.

```
// Before
abstract type RequirementSafety extends Requirement
{
  safety Asil
}

// After
abstract type RequirementSafety extends Requirement {
  safety Asil
}
```

---

### R07 — No blank lines inside blocks

**Rule:** No blank lines inside `enum`, `type`, `abstract type`, `tuple`,
`checks`, or record object `{}` blocks.
Exception: `section` blocks use R15 and intentionally include one blank line
after `{` and before `}`.

**Rationale:** Blocks are compact units — blank lines inside them break the
visual grouping and add unnecessary vertical space.

```
// Before
enum Asil {

  QM

  B

}

// After
enum Asil {
  QM
  B
}
```

---

### R08 — Block column alignment between name and type

**Rule:** Within a `type` or `tuple` body, the type token of all field/component
declarations is aligned to the same column. The column is computed as:

```
alignWidth = ⌈(longestName + trlcAttributeGap) / tabWidth⌉ × tabWidth
```

where `longestName` counts the effective name including ` optional` if present,
`trlcAttributeGap` is the minimum gap (default 2), and the result is snapped to
the nearest `tabWidth` multiple (default 4).

**Rationale:** Column alignment makes field declarations easy to scan without
the fragility of manual alignment — the formatter recomputes the column
automatically when field names change.

```
// Before
abstract type Requirement {
  description             String    // padded with spaces to align
  version                 Integer
  note optional           String
}

// After
abstract type Requirement {
    description     String    // column 16: ceil((13+2)/4)*4
    version         Integer
    note optional   String
}
```

`freeze` fields and comments are not measured and not aligned.

Controlled by option `trlcNormalizeAttributes` (default `true`). Set to `false`
to preserve source spacing verbatim.
The minimum gap before snapping is `trlcAttributeGap` (default `2`).

---

### R09 — Single space around `=` in attribute assignments

**Rule:** Exactly one space before and after `=` in attribute assignments.

**Rationale:** Consistent spacing around operators is a universal formatting
standard that improves readability.

```
// Before
ReqSpec.FeatReq FEAT_001 {
  description="The component shall..."   // no spaces
  version=1
}

// After
ReqSpec.FeatReq FEAT_001 {
  description = "The component shall..."
  version = 1
}
```

---

### R10 — No blank line before closing brace `}`

**Rule:** The closing brace `}` must immediately follow the last item in the
block with no blank line before it.

**Rationale:** Blank lines before `}` are unnecessary and inconsistent.

```
// Before
ReqSpec.FeatReq FEAT_001 {
  description = "..."
  version = 1

}        // blank line before }

// After
ReqSpec.FeatReq FEAT_001 {
  description = "..."
  version = 1
}
```

---

## RSL-specific Rules

---

### R11 — `optional` keyword position

**Rule:** The `optional` keyword comes immediately after the attribute name,
before the type.

**Rationale:** Consistent ordering of `optional` makes attribute declarations
predictable and easy to scan.

```
// Before
  String optional note    // type before optional - wrong order

// After
  note optional String
```

---

### R12 — `freeze` keyword formatting

**Rule:** `freeze <field> = <value>` on a single line, with single spaces.

```
// Before
  freeze status=Status.valid

// After
  freeze status = Status.valid
```

---

### R13 — `extends` keyword stays on same line

**Rule:** `extends TypeName` must be on the same line as the `type` keyword.

```
// Before
type FeatReq
  extends RequirementSafety {

// After
type FeatReq extends RequirementSafety {
```

---

### R14 — `checks` block formatting

**Rule:** Each check expression is indented by one `tabWidth` (default 4 spaces)
inside the `checks` block. When a check has continuation lines (severity,
message, field reference, or category), they are indented by a second level
(2× `tabWidth` from the block edge).

```
// Before
checks Requirement {
not matches(description, "(shall|should)"),
    warning "The description must include (shall|should)",
            description
}

// After
checks Requirement {
    not matches(description, "(shall|should)"),
        warning "The description must include (shall|should)",
        description
}
```

---

## TRLC-specific Rules

---

### R15 — `section` block: blank line after `{` and before `}`

**Rule:** Inside a `section` block, add one blank line after `{` and one blank
line before `}`. This separates the section header from its content.

**Rationale:** Sections are grouping constructs — the blank lines make the
content easier to read, especially with nested sections.

```
// Before
section "Feature Requirements" {
  ReqSpec.FeatReq FEAT_001 {
    description = "..."
  }
}

// After
section "Feature Requirements" {

  ReqSpec.FeatReq FEAT_001 {
    description = "..."
  }

}
```

---

### R16 — Space before `{` in record objects

**Rule:** One space between the record name and `{`.

```
// Before
ReqSpec.FailureMode SampleFailureMode{   // no space before {

// After
ReqSpec.FailureMode SampleFailureMode {
```

---

### R17 — Array values: space inside brackets and after comma

**Rule:** In non-empty array literals `[...]`, a single space follows each
comma, and there is one space after `[` and before `]`.
Empty arrays remain `[]`.  This applies equally to reference arrays and string
arrays.

```
// Before
derived_from = [SampleReq.ASR_001@1,SampleReq.ASR_002@1]
tags = ["a","b","c"]

// After
derived_from = [ SampleReq.ASR_001@1, SampleReq.ASR_002@1 ]
tags = [ "a", "b", "c" ]
```

---

### R18 — String values preserved as-is

**Rule:** String content inside `"..."`, triple-double-quoted `"""..."""`, and
triple-single-quoted `'''...'''` values is never modified, re-wrapped, or
reformatted. The formatter must treat string content as opaque value data.

**Rationale:** String values are requirement text — modifying whitespace,
indentation, or line breaks inside them would change the actual requirement
content, which is unacceptable in a safety-critical context.

This rule has **no before/after** — it is a **constraint**, not a
transformation. It defines what the formatter must **NOT** do.

The formatter only fixes the assignment syntax **around** the string,
never the content **inside** it:

```
// Before — wrong spacing around = AND unusual content inside string
description="The system shall ensure   proper   lifecycle
             management"

// After — = spacing fixed (R09 applied), string content UNTOUCHED
description = "The system shall ensure   proper   lifecycle
             management"
//            ↑ internal spaces and line break preserved exactly
```

---

## Summary Table

| ID | Rule | Applies to |
|----|------|------------|
| R01 | 4-space indentation, no tabs | Both |
| R02 | No trailing whitespace | Both |
| R03 | Single blank line between top-level declarations | Both |
| R04 | Blank line after `package` and last `import` | Both |
| R05 | One `import` per line, sorted alphabetically, no blank lines between | Both |
| R06 | Opening `{` on same line as declaration | Both |
| R07 | No blank lines inside blocks | Both |
| R08 | Block column alignment: name and type aligned per-block | Both |
| R09 | Single space around `=` | Both |
| R10 | No blank line before closing `}` | Both |
| R11 | `optional` keyword after attribute name (included in alignment width) | RSL |
| R12 | `freeze` keyword formatting | RSL |
| R13 | `extends` on same line as `type` | RSL |
| R14 | `checks` block indentation | RSL |
| R15 | Blank line after `{` and before `}` in `section` | TRLC |
| R16 | Space before `{` in record objects | TRLC |
| R17 | Space after comma and inside brackets in array literals | TRLC |
| R18 | String values preserved as-is | TRLC |

---

## Additional formatting behaviors

The following behaviors are implemented but do not have a dedicated rule number
because they are structural constraints of the grammar rather than style choices.

### Tuple separators

Inside `tuple` declarations, `separator` lines are formatted as:
```
separator <symbol>
```
with no extra spaces. The separator symbol text is preserved verbatim.
Separators participate in the block (R07, no blank lines) but are excluded from
the R08 alignment computation.

### Tuple value separators

Tuple values with a separator symbol (e.g., `A@1`) are printed with no spaces
around the separator: `element<sep>element`.

### Quantified expressions

Quantified expressions are printed on a single line:
```
(forall <var> in <source> => <body>)
(exists <var> in <source> => <body>)
```

### Conditional expressions

Conditional (`if/then/elsif/else`) expressions are printed on a single line:
```
(if <cond> then <then> elsif <cond> then <then> else <else>)
```

### Described names

Type and tuple names may include an inline description string:
```
type Requirement "A stakeholder requirement" {
```
The name and description are separated by a single space. The description
string is preserved verbatim.
