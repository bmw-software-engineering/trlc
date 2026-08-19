# TRLC Markdown Requirements Writing Guide

This guide is for requirement authors who write `.trlc.md` content.

It explains how to structure requirement documents and which Markdown constructs are supported by the parser.

## Purpose

Use `.trlc.md` when you want to define TRLC requirements in Markdown while keeping content readable for reviewers.

## Minimal File Shape

```md
# PackageName
import SomePackage

## Section title

<hr>

### RecordIdentifier
| Property | Value |
|----------|-------|
| type     | Requirement |
| asil     | SomePackage.ASIL.B |

#### top_level
true

#### description
This is a multi-line field value.
You can continue writing text on multiple lines.

<hr><br><hr>
```

## Supported Syntax and Behavior

| Markdown construct                    | Meaning                                    | Rule / Constraint                                                                                                                                     | Description                                                                                                                                                                                         |
| ------------------------------------- | ------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `# PackageName`                       | Package declaration                        | Must be exactly one identifier-safe token (letters/digits/underscore, starting with letter).                                                          | Groups and organizes all requirements defined in the file under one namespace. Can be imported by other `.trlc.md` files to reference its types and values.                                         |
| `import pkg`                          | Import package declaration                 | Allows zero or more imports, directly after the package declaration.                                                                                  | Makes the types and enum values defined in another package available in current files. Each `import` statement accepts exactly one package name; use multiple `import` lines for multiple packages. |
| `## SectionName`                      | Section declaration                        | Optional. Opens a TRLC section block; previous section is closed automatically.                                                                       | Acts as a logical grouping container within a package. All `###` requirements that follow belong to this section until a new section.                                                               |
| `### RequirementName`                 | Requirement/record name declaration        | Heading text must already be a valid TRLC identifier.                                                                                                 | Declares a named requirement object. The name is the unique identifier of this requirement within the package and section.                                                                          |
| Requirement property table            | Requirement property and field assignments | Mandatory under each `###`. Table should follow this format: `\| Property \| Value \|`, `\|----\|----\|`, then one or more `\| key \| value \|` rows. | Defines key-value properties for the requirement/record. The header and separator are for table structure/readability, and each data row maps to a field assignment.                                |
| `type` property row                   | Requirement/record type declaration        | Mandatory once per requirement block; value must match the record type name defined in RSL (case-sensitive).                                          | Record is opened only when the `type` row is found. Without it, the requirement block is skipped.                                                                                                   |
| `#### FieldName` + single scalar line | Field assignment (scalar)                  | One-line scalar values can be inferred as enum/boolean/number.                                                                                        | Useful for short typed values.                                                                                                                                                                      |
| `#### FieldName` + multi-line block   | Field assignment (string block)            | Preserves raw paragraph/list/table/link content as one string block; trims only leading/trailing blank lines.                                         | Useful for long-form fields such as descriptions.                                                                                                                                                   |
| `<hr>`                                | Visual separator                           | No parsing effect.                                                                                                                                    | Improves readability only.                                                                                                                                                                          |
| `<hr><br><hr>`                        | Visual separator between requirements      | No parsing effect.                                                                                                                                    | Improves readability only.                                                                                                                                                                          |
| Anchors and URLs                      | Plain string content                       | Preserves full literal text exactly.                                                                                                                  | Link syntax is stored as literal text; URLs are not resolved or validated by parser logic.                                                                                                          |

## Writing Rules to Follow

- Use identifier-safe names for `#`, `###`, and `####` headings.
- Always include a requirement property table under each `###` record.
- Always include a `type` row in that table.
- A property can be defined either in the property table (`| key | value |`) or using a `#### FieldName` block.
- Keep the first table row as a header row (`Property | Value`).
- Use `<hr>` and `<hr><br><hr>` only for readability.

## Tuple-Reference Arrays

Fields declared as an array of tuples can be written directly in Markdown.

**Supported layouts:**

```md
// Table cell — comma-separated
| refs | Pkg.item_a @ 1 , Pkg.item_b @ 2 |

// Table cell — <br>-separated
| refs | Pkg.item_a @ 1 <br> Pkg.item_b @ 2 |

// Field block — one per line (flexible whitespace around separator)
#### refs
Pkg.item_a @ 1
Pkg.item_b @ 2
Pkg.item_c         @         3

// Field block — comma-separated
#### refs
Pkg.item_a @ 1, Pkg.item_b @ 2
```

All LRM separator kinds are supported: `@`, `:`, `;`, and plain identifier (e.g. `covers`).

**Rules:**

- References must be package-qualified: `Pkg.item_name sep version`.
- Do **not** use bracket notation `[...]` — it conflicts with Markdown URL syntax and produces an error.

## Troubleshooting

### Error: unexpected character in heading

- Cause: `###` or `####` heading is not identifier-safe.
- Fix: rename heading to a TRLC-style identifier (for example `My_Record_Name`).

### Record skipped due to missing type

- Cause: no `type` row in the property table.
- Fix: add `| type | SomeType |`.

### Value not typed as expected

- Cause: value does not match scalar pattern, or body is multi-line.
- Fix: keep typed scalar values on a single line under `#### FieldName`.

### Error: bracket notation for tuple-reference arrays is not supported

- Cause: array value written with `[...]` (e.g. `[Pkg.item @ 1]`).
- Fix: remove the brackets and use comma or newline separation instead.

### Array field parsed as plain string

- Cause: reference is not package-qualified (e.g. `item_a @ 1` has no dot).
- Fix: write the full `Package.item_name sep version` form.

