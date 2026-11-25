# MdPlainArrayTest

## REQ_BRACKET_TABLE

| identifier | REQ_BRACKET_TABLE |
|------------|-------------------|
| type       | RequirementPlain  |
| description| Bracket notation is rejected for plain array table cells |
| numbers    | [1, 2, 3] |

<hr>

## REQ_BRACKET_FIELD

| identifier | REQ_BRACKET_FIELD |
|------------|-------------------|
| type       | RequirementPlain  |

### description
Bracket notation is rejected for plain array field blocks

### numbers
[1, 2, 3]

<hr>

## REQ_INVALID_ENTRY

| identifier | REQ_INVALID_ENTRY |
|------------|-------------------|
| type       | RequirementPlain  |
| description| An entry that is not a valid Integer |
| numbers    | 1, two, 3 |

<hr>

## REQ_INVALID_REF_ENTRY

| identifier | REQ_INVALID_REF_ENTRY |
|------------|------------------------|
| type       | RequirementPlain       |
| description| A record-reference array entry that still uses tuple syntax |
| numbers    | 1 |
| refs       | item_a @ 1 |

<hr>

## REQ_TOO_FEW_ELEMENTS

| identifier | REQ_TOO_FEW_ELEMENTS |
|------------|-----------------------|
| type       | RequirementPair       |
| description| A validly-written array that is genuinely shorter than the required minimum (not a bracket/invalid-entry rejection) |
| pair       | 5 |

<hr>

## REQ_EMPTY_ARRAY

| identifier | REQ_EMPTY_ARRAY |
|------------|------------------|
| type       | RequirementPair  |
| description| The array field is present but its value is empty (0 elements provided) |
| pair       | |

<hr>
