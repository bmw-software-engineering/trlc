# MdRefs

## Requirements

### leaf_a
| Property | Value |
|----------|-------|
| type | Requirement_Leaf |
| description | first leaf requirement |

### leaf_b
| Property | Value |
|----------|-------|
| type | Requirement_Leaf |
| description | second leaf requirement |

### req_parent_table
| Property | Value |
|----------|-------|
| type | Requirement |
| description | parent requirement |
| derived_from | [leaf_a@26](document.md#leaf_a), leaf_b |
| some_other_array_field | [leaf_a@26](document.md#leaf_a), leaf_b |

### req_parent_heading
| Property | Value |
|----------|-------|
| type | Requirement |
| description | parent requirement heading form |

### derived_from
[leaf_a@26](document.md#leaf_a)
leaf_b

### some_other_array_field
[leaf_a@26](document.md#leaf_a), leaf_b