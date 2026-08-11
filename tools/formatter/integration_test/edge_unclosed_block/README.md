# edge_unclosed_block

This test case verifies that files containing syntax errors are returned
**unchanged** (pass-through behavior).

The input contains an unclosed block (`type Broken { field String` without a
closing `}`), which causes tree-sitter to set `hasError = true` on the root
`source_file` node.

The formatter detects this in `printers.print()` and returns `options.originalText`
verbatim — the expected output therefore equals the input exactly.

This invariant is critical for safety: the formatter must never corrupt a file
that it cannot fully parse.
