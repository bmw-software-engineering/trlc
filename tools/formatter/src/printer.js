// TRLC - Treat Requirements Like Code
// Copyright (C) 2025 Bayerische Motoren Werke Aktiengesellschaft (BMW AG)
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

import { doc } from "prettier";
import { DEFAULT_ATTRIBUTE_GAP, DEFAULT_TAB_WIDTH } from "./options.js";
import { COMMENT_KINDS } from "./trlc-lexer.js";

const {
    builders: { group, hardline, ifBreak, indent, join, line, softline },
} = doc;

export const printers = {
    "trlc-ast": {
        // NOTE: Prettier's path.call / path.map recursion is used at the
        // source_file level so Prettier can track source positions for each
        // top-level declaration, enabling declaration-level range formatting.
        // Within declarations the printer walks the tree-sitter CST directly
        // to avoid a full AST-conversion layer and keep comment handling simple
        // (tree-sitter exposes comments as named children at their lexical
        // position).
        print(path, options, print) {
            const node = path.getValue();
            // Never reformat a file with syntax errors: returning it verbatim
            // guarantees the formatter cannot lose or corrupt content on invalid
            // input. Only well-formed files are reformatted.
            if (node.hasError) {
                return options.originalText;
            }
            // Route source_file through path-based recursion so Prettier
            // maintains position tracking for each top-level declaration.
            if (node.type === "source_file") {
                return printSourceFile(path, options, print);
            }
            return printNode(node, options);
        },
    },
};

// ---------------------------------------------------------------------------
// Node helpers
// ---------------------------------------------------------------------------

// Comment node types emitted by trlc-lexer.js and attached as named children
// by trlc-parser-impl.js. Sourced from COMMENT_KINDS (trlc-lexer.js) so the
// lexer, parser, and printer share a single definition of these token kinds.
const COMMENT_TYPES = new Set([COMMENT_KINDS.LINE, COMMENT_KINDS.BLOCK]);

function isComment(node) {
    return COMMENT_TYPES.has(node.type);
}

function named(node) {
    return node.namedChildren;
}

function field(node, name) {
    return node.childForFieldName(name);
}

/**
 * Like field(), but throws a descriptive error when the named field is absent.
 * Use for fields that are structurally required by the grammar — a null here
 * indicates a grammar/printer mismatch that should surface immediately.
 *
 * @throws {Error} if `node` is null/undefined, or if the named field is absent.
 */
function safeField(node, name) {
    if (node === null || node === undefined) {
        throw new Error(
            `[trlc-printer] safeField("${name}"): node is null or undefined. ` +
            `This indicates a grammar/printer mismatch.`
        );
    }
    const child = node.childForFieldName(name);
    if (child === null || child === undefined) {
        throw new Error(
            `[trlc-printer] Expected field "${name}" on ${node.type} node ` +
            `(row ${node.startPosition?.row ?? "?"}), but it was absent. ` +
            `This indicates a grammar/printer version mismatch.`
        );
    }
    return child;
}

/** Operator tokens (anonymous children) joined with single spaces. */
function operatorText(node) {
    return node.children
        .filter((c) => !c.isNamed)
        .map((c) => c.text)
        .join(" ");
}

/**
 * Return `node`'s first named child, throwing a descriptive error if there
 * isn't one. Use for grammar constructs that always have at least one named
 * child (e.g. parenthesized_expression, enumeration_literal, the object side
 * of member_expression) so a mismatched grammar shape surfaces as a clear
 * printer error instead of an unhandled TypeError from printNode(undefined).
 */
function firstNamedChild(node, label) {
    const child = node.namedChildren[0];
    if (child === undefined) {
        throw new Error(
            `[trlc-printer] ${label} has no named children ` +
            `at row ${node.startPosition?.row ?? "?"}.`
        );
    }
    return child;
}

// ---------------------------------------------------------------------------
// Main dispatch — handler map + printNode
// ---------------------------------------------------------------------------

// Maps each tree-sitter node type to a function (node, options) => doc.
// Adding support for a new grammar node means adding one entry here — no
// changes to printNode itself are required.
const NODE_PRINTERS = {
    // ── Preamble ────────────────────────────────────────────────────────
    // R04: blank line after package declaration — handled by separator().
    "package_declaration": (node) =>
        ["package ", safeField(node, "name").text],

    // R05: no blank lines between consecutive imports — handled by separator().
    "import_clause": (node) =>
        ["import ", safeField(node, "name").text],

    // ── Sections ────────────────────────────────────────────────────────
    // R15: no space between 'section' keyword and name. See FORMATTING_RULES.md §R15
    "section_declaration": (node, options) => {
        const entries = named(node).filter((c) => c.type !== "string");
        return [
            "section ",
            safeField(node, "name").text,
            printBody(entries, options, { pad: true }),
        ];
    },

    // ── Enumerations ────────────────────────────────────────────────────
    "enumeration_declaration": (node, options) => {
        const body = named(node).filter(
            (c) => c.type === "enumeration_literal" || isComment(c)
        );
        return [
            "enum ",
            printDescribedName(safeField(node, "name")),
            printBody(body, options),
        ];
    },

    "enumeration_literal": (node, options) =>
        printNode(firstNamedChild(node, "enumeration_literal"), options),

    // ── Tuples ──────────────────────────────────────────────────────────
    "tuple_declaration": (node, options) => {
        const body = named(node).filter(
            (c) =>
                c.type === "field_declaration" ||
                c.type === "separator_declaration" ||
                isComment(c)
        );
        const alignWidth = computeFieldAlignWidth(body, options);
        return [
            "tuple ",
            printDescribedName(safeField(node, "name")),
            printAlignedBody(body, options, alignWidth),
        ];
    },

    "field_declaration": (node, options) =>
        printFieldOrComponent(node, options, 0),

    "separator_declaration": (node) =>
        ["separator ", node.namedChildren.map((c) => c.text).join("")],

    "separator_symbol": (node) => node.text,

    // ── Records ─────────────────────────────────────────────────────────
    "record_declaration": (node, options) =>
        printRecordDeclaration(node, options),

    "component_declaration": (node, options) =>
        printFieldOrComponent(node, options, 0),

    "component_freezing": (node, options) => [
        "freeze ",
        safeField(node, "component").text,
        " = ",
        printNode(safeField(node, "value"), options),
    ],

    "union_type": (node, options) => [
        "[",
        join(
            ", ",
            named(node)
                .filter((c) => c.type === "qualified_name")
                .map((c) => printNode(c, options))
        ),
        "]",
    ],

    "array_declaration": (node) => [
        "[",
        safeField(node, "lower").text,
        " .. ",
        safeField(node, "upper").text,
        "]",
    ],

    // ── Checks ──────────────────────────────────────────────────────────
    "check_block": (node, options) => [
        "checks ",
        safeField(node, "target").text,
        printBody(
            named(node).filter(
                (c) => c.type === "check_declaration" || isComment(c)
            ),
            options
        ),
    ],

    "check_declaration": (node, options) =>
        printCheckDeclaration(node, options),

    "severity": (node) => node.text,

    // ── Record objects (TRLC) ────────────────────────────────────────────
    // R16: space before '{'. See FORMATTING_RULES.md §R16
    "record_object_declaration": (node, options) => [
        printNode(safeField(node, "type"), options),
        " ",
        safeField(node, "name").text,
        printBody(
            named(node).filter(
                (c) => c.type === "field_assignment" || isComment(c)
            ),
            options
        ),
    ],

    // R09: space around '=' in field assignments. See FORMATTING_RULES.md §R09
    "field_assignment": (node, options) => [
        safeField(node, "name").text,
        " = ",
        printNode(safeField(node, "value"), options),
    ],

    // ── Values ──────────────────────────────────────────────────────────
    "array_value": (node, options) => {
        const elems = named(node);
        if (elems.length === 0) return "[]";
        // R17: space after [ and before ] with comma-space between items.
        // Arrays always render on a single line regardless of length.
        return ["[ ", join(", ", elems.map((c) => printNode(c, options))), " ]"];
    },

    "tuple_value": (node, options) => {
        const sep = node.namedChildren.find(
            (c) => c.type === "separated_tuple_value"
        );
        if (sep) return printNode(sep, options);
        const elems = named(node);
        return ["(", join(", ", elems.map((c) => printNode(c, options))), ")"];
    },

    // Emit element/separator/element with no surrounding spaces (e.g. A@1).
    "separated_tuple_value": (node, options) =>
        node.children.map((c) => (c.isNamed ? printNode(c, options) : c.text)),

    // ── Expressions ─────────────────────────────────────────────────────
    "binary_expression": (node, options) => {
        if (node.namedChildren.length < 2) {
            throw new Error(
                `[trlc-printer] binary_expression has ${node.namedChildren.length} named ` +
                `children (expected 2) at row ${node.startPosition?.row ?? "?"}.`
            );
        }
        const [left, right] = node.namedChildren;
        return [
            printNode(left, options),
            " ",
            operatorText(node),
            " ",
            printNode(right, options),
        ];
    },

    "unary_expression": (node, options) => {
        if (node.namedChildren.length < 1) {
            throw new Error(
                `[trlc-printer] unary_expression has no named children ` +
                `at row ${node.startPosition?.row ?? "?"}.`
            );
        }
        const operand = node.namedChildren[0];
        return [operatorText(node), " ", printNode(operand, options)];
    },

    "parenthesized_expression": (node, options) =>
        ["(", printNode(firstNamedChild(node, "parenthesized_expression"), options), ")"],

    "conditional_expression": (node, options) =>
        printConditional(node, options),

    "quantified_expression": (node, options) => {
        // The parser stores only the quantifier keyword as an anonymous child;
        // '(', 'in', '=>', ')' are hardcoded as string literals in the output.
        const quantifier = node.children
            .filter((c) => !c.isNamed)
            .find((c) => c.text === "forall" || c.text === "exists");
        if (!quantifier) {
            throw new Error(
                `[trlc-printer] quantified_expression missing forall/exists ` +
                `at row ${node.startPosition?.row ?? "?"}.`
            );
        }
        return [
            "(",
            quantifier.text,
            " ",
            safeField(node, "variable").text,
            " in ",
            printNode(safeField(node, "source"), options),
            " => ",
            printNode(safeField(node, "body"), options),
            ")",
        ];
    },

    "member_expression": (node, options) => [
        printNode(firstNamedChild(node, "member_expression"), options),
        ".",
        safeField(node, "member").text,
    ],

    "index_expression": (node, options) => [
        printNode(safeField(node, "object"), options),
        "[",
        printNode(safeField(node, "index"), options),
        "]",
    ],

    "call_expression": (node, options) => {
        const fn = safeField(node, "function");
        const args = field(node, "arguments");
        const argDocs = args
            ? args.namedChildren.map((c) => printNode(c, options))
            : [];
        // Wrap arguments with group+softline so they break at printWidth.
        return group([
            printNode(fn, options),
            "(",
            indent([softline, join([",", line], argDocs)]),
            softline,
            ")",
        ]);
    },

    // ── Names, literals, leaves ──────────────────────────────────────────
    "described_name": (node) => printDescribedName(node),

    // Simple text-passthrough nodes — no transformation needed.
    "qualified_name": (node) => node.text,
    "identifier": (node) => node.text,
    "builtin_type": (node) => node.text,
    "integer": (node) => node.text,
    "decimal": (node) => node.text,
    "boolean": (node) => node.text,
    "null": (node) => node.text,
    "double_quoted_string": (node) => node.text,
    "triple_double_quoted_string": (node) => node.text,
    "triple_single_quoted_string": (node) => node.text,

    "string": (node, options) =>
        node.namedChildren.length
            ? printNode(node.namedChildren[0], options)
            : node.text,

    // Strip trailing whitespace from line comments (R02).
    // See FORMATTING_RULES.md §R02
    [COMMENT_KINDS.LINE]: (node) => node.text.replace(/\s+$/, ""),

    [COMMENT_KINDS.BLOCK]: (node) => node.text,

    // ERROR nodes inside a structurally valid file (hasError is false on the
    // root) are BOM-residue or other zero-content tokens that isDroppableError
    // was not able to filter out.  Emit verbatim so no content is lost.
    "ERROR": (node) => node.text,
};

/**
 * Dispatch to the appropriate handler for a tree-sitter node.
 *
 * The hasError guard is belt-and-suspenders: in normal operation printNode is
 * only reached when source_file.hasError is false (ensured by printers.print),
 * so no descendant can have an error.  If a node with errors somehow reaches
 * here (e.g., via direct calls in tests), return its verbatim text rather than
 * throwing.
 */
function printNode(node, options) {
    if (node.hasError) return node.text;
    const handler = NODE_PRINTERS[node.type];
    if (!handler) {
        throw new Error(
            `[trlc-printer] Unhandled node type "${node.type}" ` +
            `at row ${node.startPosition?.row ?? "?"}.  ` +
            `Update NODE_PRINTERS in printer.js to handle this grammar node.`
        );
    }
    return handler(node, options);
}

// ---------------------------------------------------------------------------
// Composite printers
// ---------------------------------------------------------------------------

function printDescribedName(node) {
    const desc = node.childForFieldName("description");
    const name = safeField(node, "name").text;
    return desc ? [name, " ", desc.text] : name;
}

/**
 * Compute the type-column position for aligned field/component blocks (R08).
 *
 * Algorithm:
 *   rawMax    = max effective name width across all fields in the block
 *   alignWidth = ⌈(rawMax + trlcAttributeGap) / tabWidth⌉ × tabWidth
 *
 * Returns 0 when trlcNormalizeAttributes is false (verbatim mode).
 */
function computeFieldAlignWidth(children, options) {
    if (options.trlcNormalizeAttributes === false) return 0;
    const tabWidth = options.tabWidth ?? DEFAULT_TAB_WIDTH;
    const minGap = Math.max(0, options.trlcAttributeGap ?? DEFAULT_ATTRIBUTE_GAP);

    let rawMax = 0;
    for (const c of children) {
        if (c.type !== "component_declaration" && c.type !== "field_declaration")
            continue;
        const nameNode = safeField(c, "name");
        const nameLen = nameNode.text.length;
        const isOpt = field(c, "optional") !== null;
        rawMax = Math.max(rawMax, nameLen + (isOpt ? " optional".length : 0));
    }
    if (rawMax === 0) return 0;
    return Math.ceil((rawMax + minGap) / tabWidth) * tabWidth;
}

/**
 * Print a body block where field/component nodes are aligned to alignWidth.
 * Non-field nodes (separator, freeze, comments) are printed normally.
 * Falls back to printBody when alignWidth is 0.
 */
function printAlignedBody(children, options, alignWidth) {
    if (alignWidth === 0) return printBody(children, options);
    if (children.length === 0) return [" {", hardline, "}"];
    const printed = children.map((c) => {
        if (c.type === "component_declaration" || c.type === "field_declaration")
            return printFieldOrComponent(c, options, alignWidth);
        return printNode(c, options);
    });
    return [" {", indent([hardline, join(hardline, printed)]), hardline, "}"];
}

function printFieldOrComponent(node, options, alignWidth = 0) {
    const nameNode = safeField(node, "name");
    const nameParts = printDescribedName(nameNode);
    const isOptional = field(node, "optional") !== null;
    const type = safeField(node, "type");
    const arrayNode = node.namedChildren.find(
        (c) => c.type === "array_declaration"
    );

    let sep;
    if (alignWidth > 0) {
        // R08: align type column to alignWidth, snapped to tabWidth multiple.
        const effectiveLen =
            nameNode.text.length + (isOptional ? " optional".length : 0);
        const pad = " ".repeat(alignWidth - effectiveLen);
        sep = isOptional ? [" optional", pad] : pad;
    } else if (options.trlcNormalizeAttributes !== false) {
        // Single-field block or normalize=true with no siblings: single space.
        sep = isOptional ? " optional " : " ";
    } else {
        // trlcNormalizeAttributes=false: preserve verbatim spacing by slicing
        // the original source text between the name-node end and the type-node
        // start. Uses absolute offsets against options.originalText (rather
        // than offsets relative to node.startIndex) so this doesn't depend on
        // how node.text happens to have been sliced during parsing.
        const typeNode = safeField(node, "type");
        const verbatimBetween = options.originalText.slice(
            nameNode.endIndex,
            typeNode.startIndex
        );
        sep = verbatimBetween.length > 0 ? verbatimBetween : " ";
    }

    return [
        nameParts,
        sep,
        printNode(type, options),
        arrayNode ? printNode(arrayNode, options) : "",
    ];
}

function printRecordDeclaration(node, options) {
    const parts = [];
    const qualifier = node.namedChildren.find(
        (c) => c.type === "inheritance_qualifier"
    );
    if (qualifier) parts.push(qualifier.text, " ");
    parts.push("type ", printDescribedName(safeField(node, "name")));
    const parent = field(node, "parent");
    if (parent) parts.push(" extends ", printNode(parent, options));
    const body = named(node).filter(
        (c) =>
            c.type === "component_declaration" ||
            c.type === "component_freezing" ||
            isComment(c)
    );
    // R08: compute per-block column alignment, then render with aligned body.
    const alignWidth = computeFieldAlignWidth(body, options);
    parts.push(printAlignedBody(body, options, alignWidth));
    return parts;
}

function printCheckDeclaration(node, options) {
    if (node.namedChildren.length === 0) {
        throw new Error(
            `[trlc-printer] check_declaration has no named children ` +
            `at row ${node.startPosition?.row ?? "?"}.`
        );
    }
    const expr = node.namedChildren[0];
    const severity = node.namedChildren.find((c) => c.type === "severity");
    const message = safeField(node, "message");
    const details = field(node, "details");
    const category = field(node, "category");

    const hasExtra = severity || details || category;

    if (!hasExtra) {
        return [printNode(expr, options), ", ", message.text];
    }

    const continuation = [];
    continuation.push(
        severity ? [severity.text, " ", message.text] : message.text
    );
    if (details) continuation.push(details.text);
    if (category) continuation.push(category.text);

    return [
        printNode(expr, options),
        ",",
        indent([hardline, join([",", hardline], continuation)]),
    ];
}

function printConditional(node, options) {
    const parts = ["(if ", printNode(safeField(node, "condition"), options)];
    parts.push(" then ", printNode(safeField(node, "then"), options));
    // childrenForFieldName is standard tree-sitter API (available since v0.20).
    const elsifConds = node.childrenForFieldName("elsif_condition");
    const elsifThens = node.childrenForFieldName("elsif_then");
    if (elsifConds.length !== elsifThens.length) {
        throw new Error(
            `[trlc-printer] conditional_expression has ${elsifConds.length} elsif_condition(s) ` +
            `but ${elsifThens.length} elsif_then(s) at row ${node.startPosition?.row ?? "?"}. ` +
            `This indicates a grammar/printer version mismatch.`
        );
    }
    for (let i = 0; i < elsifConds.length; i++) {
        parts.push(
            " elsif ",
            printNode(elsifConds[i], options),
            " then ",
            printNode(elsifThens[i], options)
        );
    }
    parts.push(" else ", printNode(safeField(node, "else"), options), ")");
    return parts;
}

// ---------------------------------------------------------------------------
// Block bodies + top-level structure
// ---------------------------------------------------------------------------

/**
 * Print a `{ ... }` block body. Children are separated by single hardlines
 * (no blank lines inside blocks — R07). An empty body renders as `{\n}`.
 * When `pad` is set (sections), a blank line follows `{` and precedes `}`.
 */
function printBody(children, options, { pad = false } = {}) {
    if (children.length === 0) {
        return [" {", hardline, "}"];
    }
    const printed = children.map((c) => printNode(c, options));
    const inner = pad
        ? [hardline, hardline, join(hardline, printed), hardline]
        : [hardline, join(hardline, printed)];
    return [" {", indent(inner), hardline, "}"];
}

/**
 * Print the whole file: package, imports, then declarations.
 * R05: consecutive import_clause groups are sorted alphabetically
 *      (case-insensitive) when trlcSortImports is true (default).
 */
function printSourceFile(path, options, print) {
    const node = path.getValue();

    // Pair each named child with its original index (before filtering out
    // droppable error nodes or reordering imports) so path.call() can still
    // navigate to the correct namedChildren position afterwards — tracked
    // alongside each entry as it moves, rather than recovered afterwards via
    // a reverse node → index map.
    const indexed = node.namedChildren
        .map((child, originalIndex) => ({ child, originalIndex }))
        .filter((entry) => !isDroppableError(entry.child));

    // Collect entries, replacing each run of imports with a sorted group.
    const reordered = [];
    let i = 0;
    while (i < indexed.length) {
        if (indexed[i].child.type === "import_clause") {
            // Gather the entire consecutive import run.
            const run = [];
            while (i < indexed.length && indexed[i].child.type === "import_clause") {
                run.push(indexed[i++]);
            }
            if (options.trlcSortImports !== false) {
                run.sort((a, b) =>
                    safeField(a.child, "name").text
                        .toLowerCase()
                        .localeCompare(safeField(b.child, "name").text.toLowerCase())
                );
            }
            reordered.push(...run);
        } else {
            reordered.push(indexed[i++]);
        }
    }

    const out = [];
    for (let j = 0; j < reordered.length; j++) {
        const cur = reordered[j].child;
        if (j > 0) {
            out.push(...separator(reordered[j - 1].child, cur));
        }
        // Use path.call() with the original namedChildren index so Prettier
        // maintains accurate source-position tracking for each declaration,
        // enabling declaration-level range formatting.
        out.push(path.call(print, "namedChildren", reordered[j].originalIndex));
    }
    out.push(hardline);
    return out;
}

/** True for zero-content ERROR nodes such as a stray BOM before a keyword. */
function isDroppableError(node) {
    // The character class covers:
    //   \uFEFF  — BOM
    //   \s      — ASCII whitespace (space, tab, LF, CR, FF)
    //   \u00A0  — non-breaking space
    //   \u2000-\u200B — Unicode spaces (en-space, em-space, thin-space, etc.)
    //   \u202F  — narrow no-break space
    //   \u205F  — medium mathematical space
    //   \u3000  — ideographic space
    return node.type === "ERROR" && node.text.replace(/[\uFEFF\s\u00A0\u2000-\u200B\u202F\u205F\u3000]/g, "") === "";
}

function separator(prev, cur) {
    const blank = [hardline, hardline];
    const single = [hardline];

    // A package declaration always stands alone with a blank line before it.
    if (cur.type === "package_declaration") return blank;

    if (prev.type === "package_declaration") return blank;
    if (prev.type === "import_clause" && cur.type === "import_clause")
        return single;
    if (prev.type === "import_clause") return blank;

    // A comment attaches to the declaration that follows it (no blank line).
    if (isComment(prev)) return single;

    return blank;
}
