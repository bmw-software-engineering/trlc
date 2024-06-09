# Dot separators

Because of decimals, we can't use `.` as a separator in a tuple
without massive ambiguity. This is a big proposal on how to enable
them.

## Tokens

Remove decimals as tokens.

Add a property to tokens indicating if they are surrounded by
whitespace/newline/EOF on either side.

## Tuples

Add `.` as a separator.

Add a section reference as example, e.g:

```
tuple Section_Reference {
   chapter Integer

   separator .
   section Integer

   separator .
   subsection optional Integer

   separator .
   subsubsection optional Integer
}
``

## Expressions

Remove DECIMAL from primaries, replace with decimal_expression:

```bnf
decimal_expression ::= INTEGER '.' INTEGER
```

And make a note that the `.` token must not be surrounded by
whitespace.

## Values

Replace DECIMAL with decimal_expression

Add note that resolving the ambiguity in tuple_aggregate and value
requires you to know what type you're expecting. Add a note somewhere
that the language is no longer context free.
