// TRLC - Treat Requirements Like Code
// Copyright (C) 2026 Bayerische Motoren Werke Aktiengesellschaft (BMW AG)
//
// This file is part of the TRLC Prettier formatter tool.
//
// TRLC is free software: you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// TRLC is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with TRLC. If not, see <https://www.gnu.org/licenses/>.

import assert from "node:assert/strict";
import test from "node:test";

import { format } from "prettier";
import * as trlc from "./index.js";

async function fmt(src, opts = {}) {
    return format(src, { plugins: [trlc], parser: "trlc", tabWidth: 4, ...opts });
}

// ---------------------------------------------------------------------------
// Record objects (TRLC) — R01 (4-space indent), R09 (= spacing)
// ---------------------------------------------------------------------------

test("formats a record object with normalized spacing", async () => {
    const input = "package Demo\n\nType.Rec Obj {\nname=1\n}\n";
    const expected = "package Demo\n\nType.Rec Obj {\n    name = 1\n}\n";
    assert.equal(await fmt(input), expected);
});

test("preserves triple-quoted string interior verbatim", async () => {
    const input = "package P\n\nT o {\n  d = '''keep   spacing'''\n}\n";
    const expected = "package P\n\nT o {\n    d = '''keep   spacing'''\n}\n";
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// Array values — R17 ([ elem1, elem2 ] inner spaces)
// ---------------------------------------------------------------------------

test("normalizes array element spacing — adds inner spaces (R17)", async () => {
    const input = 'package P\n\nT o {\n  tags = ["a","b","c"]\n}\n';
    const expected = 'package P\n\nT o {\n    tags = [ "a", "b", "c" ]\n}\n';
    assert.equal(await fmt(input), expected);
});

test("empty array stays []", async () => {
    const input = "package P\n\nT o {\n  tags = []\n}\n";
    const expected = "package P\n\nT o {\n    tags = []\n}\n";
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// Import sorting — R05
// ---------------------------------------------------------------------------

test("sorts imports alphabetically (R05)", async () => {
    const input = "package P\nimport ZZZ\nimport AAA\nimport MMM\n\nT o {\n  x = 1\n}\n";
    const expected = "package P\n\nimport AAA\nimport MMM\nimport ZZZ\n\nT o {\n    x = 1\n}\n";
    assert.equal(await fmt(input), expected);
});

test("keeps blank line after package and none between imports", async () => {
    const input = "package P\nimport A\nimport B\n\ntype T {\n  x Integer\n}\n";
    // type T: x(1) → alignWidth=4 → x + 3sp = "x   Integer"
    const expected = "package P\n\nimport A\nimport B\n\ntype T {\n    x   Integer\n}\n";
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// Block column alignment — R08 / R11
// ---------------------------------------------------------------------------

test("aligns type columns per-block (R08)", async () => {
    // description(11), version(7) → rawMax=11, alignWidth=16
    const input = "package P\n\ntype A {\ndescription String\nversion Integer\n}\n";
    const expected =
        "package P\n\ntype A {\n" +
        "    description     String\n" +
        "    version         Integer\n" +
        "}\n";
    assert.equal(await fmt(input), expected);
});

test("includes optional keyword in alignment width (R08/R11)", async () => {
    // note optional(13), version(7) → rawMax=13, alignWidth=16
    const input = "package P\n\ntype A {\nnote optional String\nversion Integer\n}\n";
    const expected =
        "package P\n\ntype A {\n" +
        "    note optional   String\n" +
        "    version         Integer\n" +
        "}\n";
    assert.equal(await fmt(input), expected);
});

test("indents record type components with alignment", async () => {
    // field(5) → rawMax=5, alignWidth=8
    const input = "package P\n\ntype A {\nfield String\n}\n";
    const expected = "package P\n\ntype A {\n    field   String\n}\n";
    assert.equal(await fmt(input), expected);
});

test("alignment is per-block, not per-file", async () => {
    // type A: x(1) → alignWidth=4; type B: longname(8) → alignWidth=12
    const input =
        "package P\n\ntype A {\nx Integer\n}\n\ntype B {\nlongname String\n}\n";
    const expected =
        "package P\n\ntype A {\n    x   Integer\n}\n\ntype B {\n    longname    String\n}\n";
    assert.equal(await fmt(input), expected);
});

test("freeze fields are not measured for alignment", async () => {
    // type with only freeze → no component_declarations → alignWidth=0 → printBody
    const input =
        "package P\n\ntype B extends A {\nfreeze  color  =  \"red\"\n}\n";
    const expected =
        "package P\n\ntype B extends A {\n    freeze color = \"red\"\n}\n";
    assert.equal(await fmt(input), expected);
});

test("trlcNormalizeAttributes=false preserves verbatim spacing", async () => {
    const input = "package P\n\ntype A {\nfield  String\n}\n";
    const result = await format(input, {
        plugins: [trlc],
        parser: "trlc",
        trlcNormalizeAttributes: false,
    });
    // Should preserve the two spaces from the source verbatim.
    assert.equal(result, "package P\n\ntype A {\n  field  String\n}\n");
});

// ---------------------------------------------------------------------------
// Tuple alignment — R08
// ---------------------------------------------------------------------------

test("formats a tuple declaration with separator", async () => {
    // x(1), y(1) → alignWidth=4
    const input =
        "package P\n\ntuple Coord {\nx Integer\nseparator @\ny Integer\n}\n";
    const expected =
        "package P\n\ntuple Coord {\n    x   Integer\n    separator @\n    y   Integer\n}\n";
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// Union type field
// ---------------------------------------------------------------------------

test("formats a union type field", async () => {
    // kind(4) → alignWidth=8
    const input = "package P\n\ntype T {\nkind [A, B, C]\n}\n";
    const expected = "package P\n\ntype T {\n    kind    [A, B, C]\n}\n";
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// check_declaration — R14
// ---------------------------------------------------------------------------

test("formats a simple check declaration (expr + message)", async () => {
    const input = "package P\n\nchecks T {\n  x > 0, \"must be positive\"\n}\n";
    const expected =
        "package P\n\nchecks T {\n    x > 0, \"must be positive\"\n}\n";
    assert.equal(await fmt(input), expected);
});

test("formats a check declaration with severity", async () => {
    const input =
        "package P\n\nchecks T {\n  x > 0, error \"must be positive\"\n}\n";
    const expected =
        "package P\n\nchecks T {\n    x > 0,\n        error \"must be positive\"\n}\n";
    assert.equal(await fmt(input), expected);
});

test("formats a check declaration with severity and details", async () => {
    const input =
        'package P\n\nchecks T {\n  x > 0, error "msg", "details"\n}\n';
    const expected =
        'package P\n\nchecks T {\n    x > 0,\n        error "msg",\n        "details"\n}\n';
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// quantified_expression
// ---------------------------------------------------------------------------

test("formats a forall quantified expression", async () => {
    const input =
        'package P\n\nchecks T {\n  (forall x in tags => x != ""), "no empty tags"\n}\n';
    const expected =
        'package P\n\nchecks T {\n    (forall x in tags => x != ""), "no empty tags"\n}\n';
    assert.equal(await fmt(input), expected);
});

test("formats an exists quantified expression", async () => {
    const input =
        'package P\n\nchecks T {\n  (exists x in tags => x == "critical"), "needs critical"\n}\n';
    const expected =
        'package P\n\nchecks T {\n    (exists x in tags => x == "critical"), "needs critical"\n}\n';
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// conditional_expression
// ---------------------------------------------------------------------------

test("formats a conditional (if/then/else) expression", async () => {
    const input =
        "package P\n\nchecks T {\n  (if x > 0 then x < 100 else true), \"range\"\n}\n";
    const expected =
        "package P\n\nchecks T {\n    (if x > 0 then x < 100 else true), \"range\"\n}\n";
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// component_freezing
// ---------------------------------------------------------------------------

test("formats a freeze declaration", async () => {
    const input =
        "package P\n\ntype B extends A {\nfreeze  color  =  \"red\"\n}\n";
    const expected =
        "package P\n\ntype B extends A {\n    freeze color = \"red\"\n}\n";
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// binary_expression and unary_expression
// ---------------------------------------------------------------------------

test("formats a binary expression", async () => {
    const input = "package P\n\nchecks T {\n  x>0 and y<10, \"range\"\n}\n";
    const expected =
        "package P\n\nchecks T {\n    x > 0 and y < 10, \"range\"\n}\n";
    assert.equal(await fmt(input), expected);
});

test("formats a unary (not) expression", async () => {
    const input = "package P\n\nchecks T {\n  not x == null, \"required\"\n}\n";
    const expected =
        "package P\n\nchecks T {\n    not x == null, \"required\"\n}\n";
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// Error handling — syntax errors returned verbatim
// ---------------------------------------------------------------------------

test("returns invalid files unchanged (no data loss)", async () => {
    const input = 'package P\n\nT o {\ndescription = "unterminated\n}\n';
    assert.equal(await fmt(input), input);
});

// ---------------------------------------------------------------------------
// Idempotency — diverse inputs
// ---------------------------------------------------------------------------

test("is idempotent for a type definition", async () => {
    const input = "package P\n\ntype A {\nfield  String\nother  Integer\n}\n";
    const once = await fmt(input);
    assert.equal(await fmt(once), once);
});

test("is idempotent for a checks block", async () => {
    const input =
        "package P\n\nchecks T {\n  x > 0, \"pos\"\n  x < 100, warning \"too big\"\n}\n";
    const once = await fmt(input);
    assert.equal(await fmt(once), once);
});

test("is idempotent for a tuple with separator", async () => {
    const input =
        "package P\n\ntuple Pair {\n  a Integer\n  separator @\n  b Integer\n}\n";
    const once = await fmt(input);
    assert.equal(await fmt(once), once);
});

test("is idempotent for a quantified expression", async () => {
    const input =
        'package P\n\nchecks T {\n  (forall x in items => x != ""), "non-empty"\n}\n';
    const once = await fmt(input);
    assert.equal(await fmt(once), once);
});

// ---------------------------------------------------------------------------
// check_declaration — category field (R14 extension)
// ---------------------------------------------------------------------------

test("formats a check declaration with category field", async () => {
    const input =
        'package P\n\nchecks T {\n  x > 0, error "must be positive", MyCategory\n}\n';
    const expected =
        'package P\n\nchecks T {\n    x > 0,\n        error "must be positive",\n        MyCategory\n}\n';
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// Custom options — trlcSortImports
// ---------------------------------------------------------------------------

test("trlcSortImports=false preserves original import order", async () => {
    const input = "package P\nimport ZZZ\nimport AAA\nimport MMM\n\nT o {\n  x = 1\n}\n";
    const result = await fmt(input, { trlcSortImports: false });
    // Imports must appear in original order: ZZZ, AAA, MMM
    const importLines = result.split("\n").filter((l) => l.startsWith("import "));
    assert.deepEqual(importLines, ["import ZZZ", "import AAA", "import MMM"]);
});

test("trlcSortImports=true (default) sorts imports alphabetically", async () => {
    const input = "package P\nimport ZZZ\nimport AAA\n\nT o {\n  x = 1\n}\n";
    const result = await fmt(input);
    const importLines = result.split("\n").filter((l) => l.startsWith("import "));
    assert.deepEqual(importLines, ["import AAA", "import ZZZ"]);
});

// ---------------------------------------------------------------------------
// Custom options — trlcAttributeGap
// ---------------------------------------------------------------------------

test("trlcAttributeGap=0 uses minimum gap (snapped to tabWidth)", async () => {
    // description(11): rawMax=11, gap=0 → alignWidth=ceil(11/4)*4=12 → pad=1 space
    // (contrast with default gap=2: alignWidth=16, pad=5 spaces)
    const input = "package P\n\ntype A {\ndescription String\n}\n";
    const result = await fmt(input, { trlcAttributeGap: 0 });
    // 1 space between description and String (minimal gap at column 12)
    assert.equal(result, "package P\n\ntype A {\n    description String\n}\n");
});

test("trlcAttributeGap=1 aligns with 1-space minimum gap", async () => {
    // x(1): rawMax=1, gap=1 → alignWidth=ceil(2/4)*4=4 → pad = 3 spaces
    const input = "package P\n\ntype A {\nx Integer\n}\n";
    const result = await fmt(input, { trlcAttributeGap: 1 });
    // alignWidth=4 → "x   Integer" (3 spaces padding to reach column 4)
    assert.equal(result, "package P\n\ntype A {\n    x   Integer\n}\n");
});

test("trlcAttributeGap=4 uses wider gap than default (2)", async () => {
    // x(1): rawMax=1, gap=4 → alignWidth=ceil(5/4)*4=8 → pad = 7 spaces
    const input = "package P\n\ntype A {\nx Integer\n}\n";
    const result = await fmt(input, { trlcAttributeGap: 4 });
    // alignWidth=8 → 7 spaces between "x" and "Integer"
    assert.equal(result, "package P\n\ntype A {\n    x       Integer\n}\n");
});

// ---------------------------------------------------------------------------
// Comment preservation
// ---------------------------------------------------------------------------

test("preserves inline line comment on a field assignment", async () => {
    const input = "package P\n\nT o {\n  name = 1 // a comment\n}\n";
    const result = await fmt(input);
    assert.equal(result, "package P\n\nT o {\n    name = 1\n    // a comment\n}\n");
});

test("preserves block comment between declarations", async () => {
    const input = "package P\n\n/* intro */\ntype A {\nx Integer\n}\n";
    const result = await fmt(input);
    assert.equal(result, "package P\n\n/* intro */\ntype A {\n    x   Integer\n}\n");
});

test("preserves line comment inside a checks block", async () => {
    const input = 'package P\n\nchecks T {\n  // guard\n  x > 0, "pos"\n}\n';
    const result = await fmt(input);
    assert.equal(result, 'package P\n\nchecks T {\n    // guard\n    x > 0, "pos"\n}\n');
});

test("preserves trailing line comment at end of file", async () => {
    const input = "package P\n\nT o {\n  x = 1\n}\n// trailing\n";
    const result = await fmt(input);
    assert.equal(result, "package P\n\nT o {\n    x = 1\n}\n\n// trailing\n");
});

// ---------------------------------------------------------------------------
// Error handling — additional verbatim pass-through cases
// ---------------------------------------------------------------------------

test("returns unterminated block comment verbatim (no data loss)", async () => {
    const input = "package P\n\n/* not closed\nT o {\n  x = 1\n}\n";
    assert.equal(await fmt(input), input);
});

test("returns file with missing closing brace verbatim (no data loss)", async () => {
    const input = "package P\n\ntype T {\n  x Integer\n";
    assert.equal(await fmt(input), input);
});

test("returns file with bare 0x literal verbatim (no data loss)", async () => {
    // "0x" with no hex digits is a LexError; file must be returned unchanged.
    const input = "package P\n\nT o {\n  val = 0x\n}\n";
    assert.equal(await fmt(input), input);
});

// ---------------------------------------------------------------------------
// Enumeration declaration
// ---------------------------------------------------------------------------

test("formats an enum declaration", async () => {
    const input = "package P\n\nenum Color {\nRed\nGreen\nBlue\n}\n";
    const expected = "package P\n\nenum Color {\n    Red\n    Green\n    Blue\n}\n";
    assert.equal(await fmt(input), expected);
});

test("is idempotent for an enum declaration", async () => {
    const input = "package P\n\nenum Color {\nRed\nGreen\nBlue\n}\n";
    const once = await fmt(input);
    assert.equal(await fmt(once), once);
});

// ---------------------------------------------------------------------------
// Index and member expressions
// ---------------------------------------------------------------------------

test("formats an index expression a[0]", async () => {
    const input = 'package P\n\nchecks T {\n  items [ 0 ] != null, "first"\n}\n';
    const expected = 'package P\n\nchecks T {\n    items[0] != null, "first"\n}\n';
    assert.equal(await fmt(input), expected);
});

test("formats a member expression a.b", async () => {
    const input = 'package P\n\nchecks T {\n  obj . field != null, "set"\n}\n';
    const expected = 'package P\n\nchecks T {\n    obj.field != null, "set"\n}\n';
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// 'not in' binary operator
// ---------------------------------------------------------------------------

test("formats a 'not in' expression", async () => {
    const input = 'package P\n\nchecks T {\n  x not in tags, "not allowed"\n}\n';
    const expected = 'package P\n\nchecks T {\n    x not in tags, "not allowed"\n}\n';
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// Zero-arg call expression
// ---------------------------------------------------------------------------

test("formats a zero-argument call expression f()", async () => {
    const input = 'package P\n\nchecks T {\n  f ( ) == true, "ok"\n}\n';
    const expected = 'package P\n\nchecks T {\n    f() == true, "ok"\n}\n';
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// Hex / binary / underscore numeric literals
// ---------------------------------------------------------------------------

test("preserves a hex literal 0xFF verbatim", async () => {
    const input = "package P\n\nT o {\n  val = 0xFF\n}\n";
    const result = await fmt(input);
    assert.equal(result, "package P\n\nT o {\n    val = 0xFF\n}\n");
});

test("preserves a binary literal 0b1010 verbatim", async () => {
    const input = "package P\n\nT o {\n  val = 0b1010\n}\n";
    const result = await fmt(input);
    assert.equal(result, "package P\n\nT o {\n    val = 0b1010\n}\n");
});

test("preserves an integer with underscore separators verbatim", async () => {
    const input = "package P\n\nT o {\n  val = 1_000_000\n}\n";
    const result = await fmt(input);
    assert.equal(result, "package P\n\nT o {\n    val = 1_000_000\n}\n");
});

// ---------------------------------------------------------------------------
// Option interaction / bounds
// ---------------------------------------------------------------------------

test("trlcNormalizeAttributes=false + trlcAttributeGap ignored (verbatim)", async () => {
    // When trlcNormalizeAttributes=false the gap option has no effect because
    // computeFieldAlignWidth returns 0 and spacing is taken verbatim from source.
    const input = "package P\n\ntype A {\nfield  String\n}\n";
    const result = await fmt(input, { trlcNormalizeAttributes: false, trlcAttributeGap: 8 });
    // Two spaces are the verbatim source spacing; they must not be expanded to 8.
    assert.equal(result, "package P\n\ntype A {\n    field  String\n}\n");
});

test("trlcAttributeGap=0 does not produce negative padding", async () => {
    // With gap=0, alignWidth = ceil(nameLen / tabWidth) * tabWidth.
    // For single-char name (len=1), gap=0 → alignWidth=4 → 3 spaces of padding.
    const input = "package P\n\ntype A {\nx Integer\n}\n";
    const result = await fmt(input, { trlcAttributeGap: 0 });
    // Exactly 3 spaces of padding between "x" and "Integer" (column 4).
    assert.equal(result, "package P\n\ntype A {\n    x   Integer\n}\n");
});

// ---------------------------------------------------------------------------
// section_declaration
// ---------------------------------------------------------------------------

test("formats a section declaration with record objects inside", async () => {
    const input =
        'package P\n\nsection "My Section" {\nT obj {\nx = 1\n}\n}\n';
    const expected =
        'package P\n\nsection "My Section" {\n\n    T obj {\n        x = 1\n    }\n\n}\n';
    assert.equal(await fmt(input), expected);
});

test("is idempotent for a section declaration", async () => {
    const input =
        'package P\n\nsection "My Section" {\n\n    T obj {\n        x = 1\n    }\n\n}\n';
    assert.equal(await fmt(input), input);
});

// ---------------------------------------------------------------------------
// abstract / final type qualifiers
// ---------------------------------------------------------------------------

test("formats an abstract type declaration", async () => {
    // name(4) → alignWidth=8
    const input = "package P\n\nabstract type Req {\nname String\n}\n";
    const expected = "package P\n\nabstract type Req {\n    name    String\n}\n";
    assert.equal(await fmt(input), expected);
});

test("formats a final type declaration", async () => {
    const input = "package P\n\nfinal type Req {\nx Integer\n}\n";
    const expected = "package P\n\nfinal type Req {\n    x   Integer\n}\n";
    assert.equal(await fmt(input), expected);
});

test("formats an abstract type with extends", async () => {
    const input = "package P\n\nabstract type SafeReq extends Req {\nsafety Integer\n}\n";
    const expected =
        "package P\n\nabstract type SafeReq extends Req {\n    safety  Integer\n}\n";
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// array_declaration (bounded component arrays)
// ---------------------------------------------------------------------------

test("formats a component with array bounds [1 .. 3]", async () => {
    // tag(3): rawMax=3, gap=2 → alignWidth=ceil(5/4)*4=8 → 5 spaces padding
    const input = "package P\n\ntype T {\ntag String [1..3]\n}\n";
    const expected = "package P\n\ntype T {\n    tag     String[1 .. 3]\n}\n";
    assert.equal(await fmt(input), expected);
});

test("formats a component with open-ended array bounds [0 .. *]", async () => {
    const input = "package P\n\ntype T {\ntag String [0..*]\n}\n";
    const expected = "package P\n\ntype T {\n    tag     String[0 .. *]\n}\n";
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// separator-based tuple values (@  :  ;)
// ---------------------------------------------------------------------------

test("formats a separator tuple value with @", async () => {
    const input = "package P\n\nT obj {\ncoord = 1@2\n}\n";
    const expected = "package P\n\nT obj {\n    coord = 1@2\n}\n";
    assert.equal(await fmt(input), expected);
});

test("is idempotent for a separator tuple value", async () => {
    const input = "package P\n\nT obj {\ncoord = 1@2\n}\n";
    const once = await fmt(input);
    assert.equal(await fmt(once), once);
});

// ---------------------------------------------------------------------------
// Decimal literals
// ---------------------------------------------------------------------------

test("preserves a decimal literal 3.14 verbatim", async () => {
    const input = "package P\n\nT o {\n  ratio = 3.14\n}\n";
    const result = await fmt(input);
    assert.equal(result, "package P\n\nT o {\n    ratio = 3.14\n}\n");
});

test("is idempotent for a decimal literal", async () => {
    const input = "package P\n\nT o {\n  ratio = 3.14\n}\n";
    const once = await fmt(input);
    assert.equal(await fmt(once), once);
});

// ---------------------------------------------------------------------------
// Multi-argument call expressions
// ---------------------------------------------------------------------------

test("formats a multi-argument call expression f(a, b)", async () => {
    const input = 'package P\n\nchecks T {\n  len(name,suffix) > 0, "ok"\n}\n';
    const expected = 'package P\n\nchecks T {\n    len(name, suffix) > 0, "ok"\n}\n';
    assert.equal(await fmt(input), expected);
});

// ---------------------------------------------------------------------------
// RSL-style file (type/enum/tuple/checks declarations only, no record
// objects) — exercises the grammar subset a .rsl file typically uses.
// ---------------------------------------------------------------------------

test("formats an RSL-style file (enum, tuple, abstract/extends types, checks)", async () => {
    const input =
        "package Req\n\nenum Severity {\nLow\nHigh\n}\n\ntuple Range {\nlo Integer\nhi Integer\n}\n\n" +
        'abstract type Base {\nid Integer\n}\n\ntype Derived extends Base {\nname String\n}\n\n' +
        'checks Derived {\nname != null, "must have name"\n}\n';
    const expected =
        "package Req\n\nenum Severity {\n    Low\n    High\n}\n\ntuple Range {\n    lo  Integer\n    hi  Integer\n}\n\n" +
        "abstract type Base {\n    id  Integer\n}\n\ntype Derived extends Base {\n    name    String\n}\n\n" +
        'checks Derived {\n    name != null, "must have name"\n}\n';
    assert.equal(await fmt(input), expected);
});

test("is idempotent for an RSL-style file", async () => {
    const input =
        "package Req\n\nenum Severity {\nLow\nHigh\n}\n\ntuple Range {\nlo Integer\nhi Integer\n}\n\n" +
        'abstract type Base {\nid Integer\n}\n\ntype Derived extends Base {\nname String\n}\n\n' +
        'checks Derived {\nname != null, "must have name"\n}\n';
    const once = await fmt(input);
    assert.equal(await fmt(once), once);
});

// ---------------------------------------------------------------------------
// tabWidth option interaction
// ---------------------------------------------------------------------------

test("scales indentation and column alignment with tabWidth=2", async () => {
    // description(11), version(7) with tabWidth=2, default gap=2:
    // rawMax=11 → alignWidth=ceil(13/2)*2=14 → "description" + 3sp, "version" + 7sp
    const input = "package P\n\ntype A {\ndescription String\nversion Integer\n}\n";
    const result = await format(input, { plugins: [trlc], parser: "trlc", tabWidth: 2 });
    assert.equal(result, "package P\n\ntype A {\n  description   String\n  version       Integer\n}\n");
});

// ---------------------------------------------------------------------------
// Line-ending handling
// ---------------------------------------------------------------------------

test("formats a CRLF-terminated file, normalizing line endings to LF", async () => {
    const input = "package P\r\n\r\ntype A {\r\nx Integer\r\n}\r\n";
    const result = await fmt(input);
    assert.equal(result, "package P\n\ntype A {\n    x   Integer\n}\n");
});

// ---------------------------------------------------------------------------
// Determinism / no cross-call state leakage
// ---------------------------------------------------------------------------

test("produces identical output across repeated independent format calls", async () => {
    const input = "package P\n\ntype A {\ndescription String\nversion Integer\n}\n";
    const results = await Promise.all([fmt(input), fmt(input), fmt(input)]);
    assert.equal(results[0], results[1]);
    assert.equal(results[1], results[2]);
});

test("a parse error on one file does not corrupt formatting of a later, valid file", async () => {
    // Formatter internals (parser instance, expression-depth counter, pending
    // comment queue) must not leak state across separate parseTrlc() calls.
    const invalid = "package P\n\ntype T {\n  x Integer\n"; // missing closing brace
    const valid = "package P\n\ntype A {\ndescription String\nversion Integer\n}\n";

    assert.equal(await fmt(invalid), invalid); // returned verbatim (parse error)

    const expectedValid =
        "package P\n\ntype A {\n    description     String\n    version         Integer\n}\n";
    assert.equal(await fmt(valid), expectedValid);
});

