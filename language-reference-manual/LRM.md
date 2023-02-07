# Language Reference Manual

## Design goals

It is important to have design goals for a language. The design goals
of TRLC are:

* The intended domain is requirements writing in an industrial
  safety-critical context, where requirements carry a lot of meta-data
  and linkage.

* Future language releases should be backwards compatible, as we
  anticipate that there will be a large body of requirements.

* Language design should be extensible and flexible for future
  changes.

* Requirement files (but not necessarily model and check files) should
  be human-readable with minimal training or understanding of the
  language.

* No business logic should be encoded in the language design.

## Roadmap

TRLC is an evolving language that we plan to extend. We would like to
identify several features that are definitely planned:

* Extend integer domain with a special `HEAD` value allowing you to
  talk about a HEAD revision instead of a specific versions.
* Add user-defined tuple types to allow e.g. a item + revision pairing
  of data.
* Add subtypes of integral or string types with special semantics
  (e.g. Markdown) or positive integers.

## Typographical convention

Non-normative text is typeset *(in parenthesis and italics)*.

## Grammar

The grammar uses the following symbols and conventions:

* `foobar` a non-terminal (production rule)
* `foobar_TYPE` same as above, but with a name (here: type) that can
  be used in the semantics description to refer to it
* `IDENTIFIER` a terminal (token) based on type
* `IDENTIFIER_component_name` same as above, but with a name (here:
  component_name) that can be used in the semantics description to
  refer to it
* `::=` definition of a production
* `'package'` a terminal (token) with an implicit type that must match
  precisely, usually used for indicating specific keywords or
  punctuation
* `|` an alternative production
* `[` ... `]` an optional (zero or one) production
* `{` ... `}` an optional repeated (zero or more) production

## Layout and file structure

There are three types of files:

* `.rls` They contains the user-defined type definitions and
  optionally user-defined warnings or checks
* `.check` They contain only user-defined warning or error messages
  for types declared in `.rsl` files
* `.trlc` They contain instances of the types (this is where your
  requirements go)

### Dynamic semantics

First, all `.rls` files are parsed. Then, if no errors are raised, all
`.check` files are parsed. Finally, if no errors are raised, all
`.trlc` files are parsed.

After all files are parsed, references are resolved and user-defined
checks are applied.

It is unspecified how an implementation treats errors in `.trlc`
files, but it is recommended to not stop processing after the first
error.

## Lexing

### Encoding

All input files are encoded in UTF-8. Passing a file with a different
encoding to TRLC results in undefined behaviour.

It is recommended to try to detect this in an implementation and raise
a fatal error; but in the interest of compatibility and sanity an
implementation shall not provide a way to switch the encoding (at the
command-line or otherwise).

### Whitespace and comments

Whitespace is ignored.

Comments are C-Style `/* .. */` and C++ style `//`, and are
ignored. The matching for C-style comments is non-greedy.

### Identifiers and keywords

Identifiers start with a letter and are followed by letters, numbers,
or underscores.

```
IDENTIFIER ::= [a-zA-Z][a-zA-Z0-9_]*
```

There is also a legacy "builtin" identifier that is deprecated. It
will be removed in a future major release.

```
BUILTIN_IDENTIFIER ::= [a-z]+:[a-zA-Z][a-zA-Z0-9_]*
```

A keyword is an identifier that is one of the following reserved
words:

* `abs`
* `and`
* `checks`
* `else`
* `elsif`
* `enum`
* `error`
* `extends`
* `false`
* `fatal`
* `if`
* `implies`
* `import`
* `in`
* `not`
* `null`
* `optional`
* `or`
* `package`
* `section`
* `then`
* `true`
* `type`
* `warning`
* `xor`

### Delimiters

Single character delimiters:

* Brackets: `(` `)` `[` `]` `{` `}`
* Punctuation: `,` `.` `=`
* Operators: `*` `/` `%` `+` `-`
* Boolean operators: `<` `>`

Double character delimiters:

* Operators: `**`
* Boolean operators: `==` `<=` `>=` `!=`
* Punctuation: `=>`

Preference is (obviously) given to longer delimiters if there is
ambiguity; i.e. `==` takes precedence over two `=` tokens.

### Integer literals

Integers are base 10, and leading zeros are effectively ignored.

```
INTEGER ::= [0-9]+
```

### String literals

There are two versions of a string, double quoted and triple quoted:

```
STRING ::= "([^"]|(\\"))*"
         | '''.*?'''
```

#### Static semantics

The value of a double quoted string is precisely the characters
between the two double quotes, with all instances of the `\"` escape
sequence being replaced with `"`.

The value of a triple quoted string is the whitespace trimmed string
of characters between the triple quotes (including the line breaks),
The common whitespace at the beginning of each line (ignoring blank
lines) starting at the second is removed. The trailing whitespace on
every line is removed. There is no escaping in a triple quoted string.

#### Examples

The value of `"foo"` is `foo`.

The value of

```
'''this is

     a wonderful
   example
'''
```

is

```
this is

  a wonderful
example
```

We can see two transformations in action here: first the trailing
whitespace (the trailing newline) is removed providing us with a
trimmed string. Then the common whitespace (three spaces) is removed
from each line starting from the second; however we ignore the blank
line.

Note that mixing tabs and spaces will have unexpected results, for
example:

```
'''
\t foo
 \tbar
'''
```

Would be displayed normally as

```
'''
         foo
        bar
'''
```

However there zero shared whitespace since (`\t ` is not the same as `
\t`), and so the resulting value of the string would be here: `foo\n
\tbar` (note that the leading whitespace for foo is still stripped).

## RLS files

A `.rls` file starts with a package declaration and is followed by
type declarations.

```
rls_file ::= package_indication
             { import_clause }
             { type_declaration | check_block }

package_indication ::= 'package' IDENTIFIER_name

import_clause ::= 'import' IDENTIFIER_name
```

### Static semantics
A package is declared in an `rls` file. Any given package name may
only appear once globally.

The package indication defines the "current package".

A package may be imported, in which case its name may be used as the
prefix of a `qualified_name`.

A package may not import itself.

In a RSL file, a package may not import a package that imports itself,
directly or indirectly.

An implementation shall support the following builtin types, that
shall be made available for all packages:

* `Boolean`
* `Integer`
* `String`

A `Boolean` has two values, false and true.

An `Integer` is a signed integer, with an implementation defined
range. *(This range can be infinite.)*

A `String` is a sequence of implementation defined characters. *(The
decision to support unicode or not is left unspecified.)* The maximum
length of a String is implementation defined, but shall be at least
1000.

A package also includes a number of builtin functions that are made
available:

* `len`
* `startswith`
* `endswith`
* `matches`

## Described names

```
described_name ::= IDENTIFIER_name [ STRING_description ]
```

### Static semantics

A described name names an entity. The optional string description has
no static or dynamic semantics.

Two described names are considered equal if their names are equal.

*(The description has no bearing on equality. The string description
should be exported to the API, so that downstream tools can make use
of it. This way we don't have to give some comments special meaning,
and we don't have to implement error-prone heuristics in downstream
tools for discovering these descriptions.)*

## Type declarations

```
type_declaration ::= 'enum' described_name enumeration_declaration
                   | 'type' described_name record_declaration
```

### Static semantics

It is an error to create a type with a name that already exists in the
current package. (Note: this especially includes shadowing one of the
builtin types.)


## Enumeration declarations

```
enumeration_declaration ::=
   '{' { enumeration_literal_specification } '}'

enumeration_literal_specification ::= described_name
```

### Static semantics

Each described name declares an enumeration literal specification,
which shall have a unique name in that enumeration.

*(It is not an error to have the same literal specification for
different enumerations.)*

*(It is not an error to have an enumeration literal with the same name
as a record or enumeration - as there is no ambiguity - but it is
recommended that an implementation emits a warning in this case.)*

### Examples

```
package Example

enum ASIL {
   QM "Not safety relevant"
   A B C D
}

enum My_Boolean {
   yes
   no
   file_not_found
}
```

## Qualified names
```
qualified_name ::= [ IDENTIFIER_package_name '.' ] IDENTIFIER_name
```

### Static semantics
The package name of a qualified name must be the current package or an
imported package.

The name must be a valid symbol in the current scope (if no package is
provided) or a valid symbol of the indicated package.


## Record declarations

```
record_declaration ::= [ 'extends' qualified_name_ROOT_TYPE ]
                       '{' { component_declaration } '}'

component_declaration ::=
   described_name [ 'optional' ]
   qualified_name_COMPONENT_TYPE  [ array_declaration ]

array_declaration ::= '[' INTEGER_lower '..' '*' ']'
                    | '[' INTEGER_lower '..' INTEGER_upper ']'
```

### Static semantics
The root type for a record extension must be a valid record type.

Each component declaration shall have a unique name in that record
declaration, or any of its root types. *(Two separate record
extensions may defined the same component, and they may even have
different types. But you cannot re-define a component from a parent
type.)*

A component with an array declaration introduces an anonymous array
type. This means the type of the record component is not the type as
specified, but rather an array where the element type is that type.

It is an error to specify an upper bound that is less than the lower
bound. *(Note that it is permitted for them to be equal.)*

Each component type shall refer to an valid type, or to the name of
the record type itself. It is an error to refer to a type that has not
been declared yet.

*(As there are no forward declarations in the language, this forces
the user type hierarchy to be a DAG, but permitting self-references.)*

### Dynamic semantics

Arrays are indexed by positive integers and the first index is 0.

An instance of an array type with star ('*') as the upper bound shall
contain at least lower bound elements.

An instance of an array with both a lower bound and an upper bound
shall contain at least lower bound elements and at most upper bound
elements.

An implementation may impose an arbitrary limit to the actual upper
bound of a list, which is enforced statically *(when declaring record
instances)*. This limit, if it exists, shall be greater than or equal
to 1000.

A record type that extends another inherits all components and user
defined checks specified for its root type. Instances of an extension
may be provided as a reference where a root type is required; but not
the other way around. *(This provide a limited form of polymorphism,
but with the liskov substitution principle guaranteed.)*

### Implementation recommendations

It is recommended to emit an error on arrays with an upper bound of zero.

It is recommended to emit a warning on arrays with an upper bound of one.


### Examples

```
type Requirement {
   summary "A short summary of the requirement."
     String

   description "The actual requirement text."
     Annotated_String

   asil optional ASIL

   codebeamer_link Integer [1..*]
}

type Supplier_Requirement extends Requirement {
   supplier_id Integer
}
```

## Check files

A `.check` file is simply a set of check blocks.

```
check_file ::= package_indication
               { check_block }
```

### Static semantics

It is an error to indicate a package that has not been declared in an
RSL file.

## Checks

```
check_block ::= 'checks' IDENTIFIER_record_name
                '{' { check_declaration } '}'

check_declaration ::= expression ',' [ severity ] STRING_message
                      [ ',' IDENTIFIER_component_name ]

severity ::= 'warning'
           | 'error'
           | 'fatal'
```

### Static semantics

It is an error to refer to a type that does not exist in the package
indicated, or is not a record type.

In a check declaration, it is an error to refer to a component name
that does not belong to the record indicated.

*(Note that it is never possible to add checks to a type from a
foreign package. In check files this is more obvious as you cannot
have an import clause, but this is also true for checks declared in
rsl files since it is not possible to specify a qalified name.)*

### Dynamic semantics

Each check is evaluated in the specified order.

If multiple check blocks are declared for the same record, then the
order of evaluation of each check block is unspecified.

For record extensions, all checks for the base record must be
evaluated before any check of the record extension is evaluated.

For each instance of the record type, each check first evaluates the
expression, with a binding of variables given by a that instance. It is
an error if the final type of the evaluated expression is not Boolean.

If the evaluated expression is true, no action is taken. If it is
false, then a message emitted with the specified message text. If a
component name is provided, then the error is anchored at the left
hand side of the assignment to that component. If no component name is
provided, then the anchoring is implementation defined.

*(A suitable anchoring for a message without a component could be the
declaration itself. If only a single component is used in the
expression then the message could be anchored the same way as if the
component was indicated explicitly in the check.)*

The severity, if provided, controls how future errors are treated, and
how the TRLC implementation terminates. A warning has no effect other
than emitting the message. An error (the default, in case severity is
not specified) causes an implementation to eventually return a
non-zero error code, but further checks will be evaluated (potentially
creating more messages). A fatal message is like an error, except that
no further checks shall be evaluated for this record instance.

*(It is an important design goal to keep the type system sane and
following LSP. I.e. each subtype may only narrow the values permitted
in a type. This means for a record R and its extension RE; any valid
instance of RE is always a valid instance of R if a new binding of R
is created considering only the fields that are in R. It will never be
possible to delete, suppress, or omit checks in record extensions.)*

### Example

```
package Example

checks Requirement {
   summary != null, warning "You should specify a summary", summary
}

check OverflowGuard {
   value >= -100, fatal "Value must be at least 0"
   value <= 100, fatal "Value must be at most 100"
   // These bound value, and effectively guard against integer
   // overflow in the below expression

   value ** 2 == 25, warning "Value is not 5 or -5"
}
```

## Expressions

```
expression ::= relation { 'and' relation }
             | relation { 'or' relation }
             | relation [ 'xor' relation ]
             | relation [ 'implies' relation ]

relation ::= simple_expression [ comparison_operator simple_expression ]
           | simple_expression [ 'not' ] 'in' membership_choice
           | simple_expression [ 'not' ] 'in' simple_expression

membership_choice ::= simple_expression '..' simple_expression

simple_expression ::= [ adding_operator ]
                      term { adding_operator term }

term ::= factor { multiplying_operator factor }

factor ::= primary [ '**' primary ]
         | 'not' primary
         | 'abs' primary

primary ::= INTEGER
          | STRING
          | 'null'
          | name
          | '(' expression ')'
          | '(' quantified_expression ')'
          | '(' conditional_expression ')'
```

### Examples

```
asil != ASIL.QM

length(summary) + length(description) > 10

description != null implies "potato" in description

(forall item in codebeamer_link => item > 50000)
```

## Names

```
name ::= qualified_name
       | qualified_name ['.' IDENTIFIER_literal]
       | name '[' expression ']'
       | IDENTIFIER_builtin_function '(' parameter_list ')'
       | BUILTIN_IDENTIFIER '(' parameter_list ')'

parameter_list ::= expression { ',' expression }
```

### Static semantics

The builtin function `len` is of arity 1. Its parameter must be of
type `String` or an array type. Its return type is `Integer`.

The builtin functions `startswith` and `endswith` are of
arity 2. All of their parameters must be of type `String`. The return
type of either function is `Boolean`.

The builtin function `matches` is of arity 2. Its parameters must
be of type `String`. The return type is `Boolean`. The function's
second parameter must be a valid regular expression. *(It is
implementation defined which regular expression language is used, but
it is highly, _highly_ recommended to implement the standard POSIX
regular expressions.)*

In addition, the second parameter to the `matches` function must
be a static compile-time constant, i.e. it must not depend on the
value of a record field or the value of a quantified variable.

### Dynamic semantics

The `len` function computes the length of the given string or array.

The `startswith` function returns true iff the first parameter
fully contains the second parameter at its start.

The `endswith` function returns true iff the first parameter
fully contains the second parameter at its end.

The `matches` function returns true iff the first parameter is
matched by the regular expression given in the second parameter.

### Name resolution
Name resolution is case sensitive.

### Implementation recommendations
The parsing of unary minus can be confusing: `-a % b` is actually `-
(a % b)`. The semantics of `%` are carefully specified so that this
does not matter. It does also mean that `-a / -b` is not legal and
needs to be written as either `-a / (-b)` or even better `(-a) /
(-b)`.

It is recommended that a linter warns whenever a unary minus is
encountered that has a non-trivial `term` or `factor` as its operand.

### Examples

```
foo          // refers to foo, whatever that may be
pkg.sym      // refers to the record object sym from pkg
pkg.sym.lit  // refers to the enum literal lit
foo[1]       // refers to the second element of foo

len("potato")                 // computes 6
startswith("potato", "p")     // returns true
matches("potato", "^P")       // returns false
matches("potato", "^" + "p")  // returns true
matches("potato", myfield)    // error: myfield is not a constant
```

## Operators
```
comparison_operator ::= '==' | '!=' | '<' | '<=' | '>' | '>='

adding_operator ::= '+' | '-'

multiplying_operator ::= '*' | '/' | '%'
```

### Static semantics

For a chain of operators of the same category, the association is left
to right.

For each builtin type, some but not necessarily all, of the above
operators are defined.

## Logical operators

There are four Boolean operators defined for expressions of Boolean
type. The type of the result is Boolean.

### Static semantics

Operators with short-cut semantics are `and`, `or`, and `implies`.

The operator with regular semantics is `xor`.

### Dynamic semantics

Short-circuit operators first evaluate the left-hand-side of the
expression and only evaluate the right-hand-side if and only if it
could influence the result.

## Relational operators and membership tests

The equality operators `==` and `!=` are defined for all types, as
long as the types are compatible.

The ordering relations `<`, `<=`, `>=`, and `>` are defined for
integers only.

Range membership tests are defined for Integers only.

Substring tests are defined for Strings only.

### Static semantics

The result type of any relational operator or membership test *(which
also includes substring tests)* is always Boolean.

An inclusive range membership test `x in a .. b` has the same meaning
as the Boolean expression `x >= a and x <= b`. *(This means if a is
less than b, it is not an error. Instead the result of the test is
always false.)*

An exclusive range membership test `x not in a .. b` has the same
meaning as the Boolean expression `x < a or x > b`.

A substring membership test has the usual definition.

## Adding operators

The binary adding operator `+` is defined for both Strings and
Integers.

The unary adding operator `+`, and the binary and unary adding
operator `-` is defined only for Integers.

### Static semantics

For binary adding operators the types of the operands have to match,
and the result is the same type as the two operands. For unary adding
operators the result is always Integer.

The binary `+` for strings is defined as String concatenation.

### Dynamic semantics

It is implementation defined if type checks (range or length) are
performed for intermediate values; if type checks are not performed
then the resulting expression must not be an error. This applies to
any operation.

(*This means you either type check all the time, or you guarantee that
any intermediate will not create an error in the implementation, as
long as the final value fits in the relevant type. For example if A
and B are maxlength Strings, then `"potato" in A + B` may either
create an error when attempting to concatenate the strings, OR it must
work correctly. What you cannot do is cause undefined behaviour in the
evaluation.)*

## Multiplying operators

The multiplying operators `*`, `/`, and `%` are defined only for
Integer types. The result is an integer.

The modulus division for `x % y` satisfies the relation `x = y*N + (x
% y)`, for some (signed) value of `N`, with one following constraints
met:

* `x % y` is `0`
* `x % y` has the same sign as `y` and an absolute value less than `y`

### Dynamic semantics

Division by zero or modulo division by 0 is an error.

## Highest precedence operators

The exponentiation operator `**` is defined for Integers only, and
returns an Integer.

The right-hand side parameter of `**` must be a static compile-time
constant, i.e. it must not depend on the value of a record field or
the value of a quantified variable. It must not be negative.

The absolute value prefix operator `abs` is defined for Integers only,
and returns a (positive) Integer.

The logical negation prefix operator `not` is defined for Booleans
only, and returns a Boolean.

### Dynamic semantics

The right-hand-side of an exponentiation must not be negative.

## Quantification

```
quantified_expression ::=
   'forall' IDENTIFIER_name 'in' IDENTIFIER_component_name '=>'
   expression
```

### Static semantics

A quantified expression introduces a new name, that is valid only
inside expression. This new name must not shadow any other.

*(This means two separate quantified expressions may use the same
name, but you may not nest and shadow, and you may not shadow a
component name either.)*

The type of the expression must be Boolean.

The component name must be defined in the current record, and must be
an array type.

The result of a quantified expression is Boolean.

### Dynamic semantics

To determine the final value of the quantified expression, each
element of the array is evaluated in sequence and its value is bound
to the declared name. The expression is then evaluated in this
binding. If that evaluation is ever false, then the final value of the
quantified expression is also false. If it is never false, then the
final value of the quantified expression is true.

*(This means any quantification over an empty array is always true.)*

## Conditionals

```
conditional_expression ::=
   'if' expression_CONDITION 'then' expression_DEPENDENT
   {'elsif' expression_CONDITION 'then' expression_DEPENDENT }
   'else' expression_DEPENDENT
```

### Static semantics

The condition expressions must be of Boolean type.

The dependent expressions must all be of the same type, and the type
of the conditional expression is also of that type.

### Dynamic semantics

Each condition is evaluated in sequence. Evaluation stops on the first
condition that evaluates to true; after which the corresponding
dependent expression is evaluated and returned.

If all condition are evaluated to false, then the else dependent
expression is evaluated and returned.

### Examples

This is the same as `foo implies bar`:
```
(if foo then bar else true)
```

This is a more complex guarded test for optionally specified fields:
```
(if    foo /= null then foo > 2
 elsif bar /= null then bar > 2
 else  True)
```

## TRLC files

A `.trlc` file is simply a set of record object declarations.

```
trlc_file ::= package_indication
              { import_clause }
              { trlc_entry }

trlc_entry ::= section_declaration
             | record_object_declaration
```

### Static semantics

It is possible to indicate a package that has not been declared in an
RSL file.

## Sections

```
section_declaration ::= 'section' STRING_section_name
                        '{' { trlc_entry } '}'
```

A section has no semantic impact, and no impact on name
resolution. Section names do not have to be unique. It may be exposed
in an API, for example to section a HTML view of requirements.

## Record object declarations

```
record_object_declaration ::=
   qualified_name IDENTIFIER_name
   '{' { component_association } '}'

component_association ::= IDENTIFIER_component_name '=' value

value ::= [ adding_operator ] INTEGER
        | STRING
        | qualified_name_RECORD_OBJECT
        | qualified_name_ENUM_TYPE '.' IDENTIFIER_enumeration_literal
        | '[' [ value { ',' value } ] ']'
```

### Static semantics

The type of the declaration must be a valid record type. If no
qualified name is given, the record type must be in the indicated
package.

The name of the declaration must be a unique name in the indicated
package. See below for additional constraints on what unique
means. The name of the declaration must not clash with a type or
package.

Each component name must be a valid component of the record type.

Each enumeration must be a valid enumeration type in the indicated (or
qualified) package. Each enumeration literal must be a valid literal
of the indicated enumeration in the prefix.

The type of each value must match each component or array element
type. Records are specified only through references (there is no way
to specify an inline anonymous instance).

It is an error to not specify a non-optional field.

The prefix of a qualified name must be imported.

### Dynamic semantics

A record object declaration creates a new binding for a record. After
references are resolved, all checks are evaluated in the context of
this binding.

It is an error to refer to a record by name that does not exist. (Note
that it is legal to refer to an object that has not been declared yet,
as references are resolved after parsing.)

A record reference must match in type, i.e. be of the correct type or
any record extension of that type. *(For example if RE extends R, then
a list of R may contain references to instances of R and RE. A list of
RE may not contain any references to R.)*

### Name resolution

When declaring record objects there are wider rules that indicate name
clashes. Specifically a record may not be declared if its "simplified
name" clashes with any other "simplified name".

A simplified name is the name converted to lowercase and all
underscored removed.

*(For example the simplified name of `Foo_Bar` is `foobar` and
therefore it clashes with `Foobar`, `F_Oobar`, or `Foo_B_A_R`. But
only at record declaration; when referring to other object you still
have to use a precise match.)*

*(The purpose of this rule is to avoid requirements that have hard to
distinguish names.)*

### API

When exposing record instances through the API, it is required to make
the type of the instance available. There are some recommendations,
none of which are required:

* Provide an implicit String record field named `type` that carries
  this information (it is safe to do that, as it is impossible to
  specify a record type with a field named `type`).

* Provide a function that, when called, provides the type information.

* Provide the type information through the type system of the API
  language (e.g. the Python type system).

## Null values

The value of an optional field that is not specified is null.

### Static semantics

The null value has a polymorphic type that matches the required type
given by context.

It is an error to form an expression if the type of all operands
cannot be statically determined. *(This means the expression `null ==
null` is not true, but an error.)*

### Dynamic semantics

For equality the null value is considered equal to itself, but not
equal to any non-null value.

For any other operator, the null value is considered out of bounds and
raises an error.

*(This means you can check if something is null or not, but any other
use will cause an error.)*
