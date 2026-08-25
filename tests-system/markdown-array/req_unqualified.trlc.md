# MdArrayTest

## Unqualified References

### REQ_UNQUAL_SINGLE

| identifier  | REQ_UNQUAL_SINGLE |
|-------------|-------------------|
| type        | RequirementAt |
| description | Single unqualified reference (same package, no prefix) |

#### refs
item_a @ 1

<hr>

### REQ_UNQUAL_MULTI

| identifier  | REQ_UNQUAL_MULTI |
|-------------|-----------------|
| type        | RequirementAt |
| description | Multiple unqualified references, comma-separated |

#### refs
item_a @ 1, item_b @ 2

<hr>

### REQ_MIXED

| identifier  | REQ_MIXED |
|-------------|-----------|
| type        | RequirementAt |
| description | Mixed: unqualified and fully qualified in one array |

#### refs
item_a @ 1, MdArrayTest.item_b @ 2

<hr>

### REQ_QUALIFIED_SAME_PKG

| identifier  | REQ_QUALIFIED_SAME_PKG |
|-------------|------------------------|
| type        | RequirementAt |
| description | Qualified with own package name — also valid |

#### refs
MdArrayTest.item_a @ 1

<hr>
