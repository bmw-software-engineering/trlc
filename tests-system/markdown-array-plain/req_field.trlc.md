# MdPlainArrayTest

## REQ_FIELD_COMMA

| identifier | REQ_FIELD_COMMA  |
|------------|------------------|
| type       | RequirementPlain |

### description
Field blocks using comma separation

### numbers
1, 2, 3

### levels
1.5, 2.5

### flags
true, false

### tags
"alpha", "beta"

### modes
Mode.Fast, Mode.Slow

### refs
MdPlainArrayTest.item_a, MdPlainArrayTest.item_b

<hr>

## REQ_FIELD_NEWLINE

| identifier | REQ_FIELD_NEWLINE |
|------------|-------------------|
| type       | RequirementPlain  |

### description
Field blocks using one entry per line

### numbers
4
5
6

### levels
0.1
0.2

### flags
false
true

### tags
"gamma"
"delta"

### modes
Mode.Slow
Mode.Fast

### refs
item_a
item_b
item_c

<hr>

## REQ_FIELD_SINGLE

| identifier | REQ_FIELD_SINGLE |
|------------|------------------|
| type       | RequirementPlain |

### description
A single-element array in each field, no comma needed

### numbers
42

### levels
3.14

### flags
true

### tags
"solo"

### modes
Mode.Fast

### refs
item_a

<hr>
