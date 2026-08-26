# MdArrayTest

## Requirements

### REQ_FIELD_A_BRACKET

| identifier  | REQ_FIELD_A_BRACKET                           |
|-------------|------------------------------------------------|
| type        | RequirementSemicolon                           |
| description | Field.A: single item with brackets using ; (should error) |

#### refs
[MdArrayTest.item_a ; 1]

<hr>

### REQ_FIELD_C_BRACKET

| identifier  | REQ_FIELD_C_BRACKET                            |
|-------------|------------------------------------------------|
| type        | RequirementWord                                |
| description | Field.C: multi-item with brackets using identifier separator (should error) |

#### refs
[MdArrayTest.item_a via 1, MdArrayTest.item_b via 2]

<hr>
