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

// Pure-JavaScript recursive-descent + Pratt expression parser for TRLC/RSL.
//
// Produces a CST whose nodes implement the same API surface as tree-sitter's
// SyntaxNode so that printer.js can consume it without modification.
//
// Entry point:
//   parseTrlc(source: string) → CSTNode   (type === "source_file")
//
// On any lex or parse error the function returns a source_file node whose
// hasError flag is true. The printer treats this as "leave verbatim", so the
// formatter never corrupts invalid or partially-written files.

import { CSTNode } from './trlc-node.js';
import { tokenize, LexError, COMMENT_KINDS } from './trlc-lexer.js';

// Maximum nesting depth accepted by parseExpression() (parenthesised/unary/
// binary chains). Guards against exhausting the JS call stack on
// pathologically nested input; exceeding this raises a normal _ParseError,
// which parseTrlc() turns into a safe "leave file verbatim" result.
const MAX_EXPRESSION_DEPTH = 500;

// Symbols that may separate tuple values (see LRM `separator_declaration` /
// `separated_tuple_value`). Shared between parseSeparatorSymbol() and
// _trySeparatorContinuation() so the accepted symbol set is defined once.
const SEPARATOR_SYMBOLS = new Set(['@', ':', ';']);

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

export function parseTrlc(source) {
    let tokens;
    try {
        tokens = tokenize(source);
    } catch (e) {
        return _errorRoot(source);
    }
    try {
        return new _Parser(source, tokens).parseSourceFile();
    } catch (e) {
        return _errorRoot(source);
    }
}

// ---------------------------------------------------------------------------
// Error root
// ---------------------------------------------------------------------------

function _errorRoot(source) {
    const lines = source.split('\n');
    const lastLine = lines[lines.length - 1];
    const root = new CSTNode(
        'source_file', source,
        0, source.length,
        { row: 0, column: 0 },
        { row: lines.length - 1, column: lastLine.length }
    );
    root.hasError = true;
    return root;
}

// ---------------------------------------------------------------------------
// Pratt parser — infix binding powers (left-binding power = lbp)
// ---------------------------------------------------------------------------

// Binary operator left-binding powers. Higher value = tighter binding.
// Derived from the tree-sitter grammar's prec.left(N, ...) / prec.right(N, ...)
// assignments.
const INFIX_BP = {
    'implies': 1,
    'or': 2, 'xor': 2,
    'and': 3,
    '==': 4, '!=': 4, '<': 4, '>': 4, '<=': 4, '>=': 4,
    'in': 4,  // 'not in' is handled specially
    '..': 5,
    '+': 5, '-': 5,
    '*': 6, '/': 6, '%': 6,
    '**': 7,  // right-associative: rbp = lbp - 1 = 6
    '.': 9,  // member access
    '(': 10,  // function call (postfix)
    '[': 10,  // array index  (postfix)
};

// Binding power used for unary prefix operators (not, -, +, abs), mirroring
// tree-sitter's prec(8, seq(...)) for unary operators. Equal to the binding
// power of '**' — the tightest-binding *binary* operator — so every regular
// binary operator has lower-or-equal binding power than a unary prefix.
// ('.', '(', '[' are postfix operators handled by their own code paths in
// parseExpression()/_tryPostfixOperator(), not by this unary precedence, so
// they are deliberately excluded from this derivation.)
const UNARY_BINDING_POWER = INFIX_BP['**'];

// Builtin TRLC type names. These are lexed as 'ident' tokens and must be
// recognised in type-declaration context to produce builtin_type nodes.
const BUILTIN_TYPES = new Set(['Boolean', 'Integer', 'Decimal', 'String', 'Markup_String']);

// Maps the current token kind to the _Parser method that parses the
// corresponding top-level declaration. Adding a new top-level grammar
// production only requires adding one entry here, instead of extending a
// switch statement.
const TOP_LEVEL_DISPATCH = {
    'enum': 'parseEnumerationDeclaration',
    'tuple': 'parseTupleDeclaration',
    'abstract': 'parseRecordDeclaration',
    'final': 'parseRecordDeclaration',
    'type': 'parseRecordDeclaration',
    'checks': 'parseCheckBlock',
    'section': 'parseSectionDeclaration',
    'ident': 'parseRecordObjectDeclaration',
};

// ---------------------------------------------------------------------------
// Parser class
// ---------------------------------------------------------------------------

class _ParseError extends Error {
    constructor(msg) { super(msg); this.name = 'ParseError'; }
}

class _Parser {
    // Sentinel returned by _tryNotIn() to signal "stop the parseExpression
    // loop" (as opposed to returning a new AST node).
    static STOP = Symbol('stop');

    constructor(source, tokens) {
        this.source = source;
        this.tokens = tokens;
        this.pos = 0;
        // Comments encountered while skipping to the next significant token
        // are queued here so the caller can flush them into the right parent.
        /** @type {CSTNode[]} */
        this.pending = [];
        // Current nesting depth of parseExpression() calls; see
        // MAX_EXPRESSION_DEPTH.
        this._exprDepth = 0;
    }

    // ── Token navigation ───────────────────────────────────────────────────

    /** Collect comment tokens into this.pending, return next real token. */
    peek() {
        while (
            this.pos < this.tokens.length &&
            (this.tokens[this.pos].kind === COMMENT_KINDS.LINE ||
                this.tokens[this.pos].kind === COMMENT_KINDS.BLOCK)
        ) {
            const tok = this.tokens[this.pos++];
            this.pending.push(this._tokNode(tok, tok.kind));
        }
        return this.tokens[this.pos];
    }

    /** Return the current token kind (after collecting pending comments). */
    peekKind() {
        return this.peek().kind;
    }

    /** Consume and return the current token (collects comments first). */
    advance() {
        this.peek();
        return this.tokens[this.pos++];
    }

    /** Consume a token of the expected kind; throw ParseError if mismatch. */
    expect(kind) {
        const tok = this.peek();
        if (tok.kind !== kind) {
            throw new _ParseError(
                `Expected '${kind}' but got '${tok.kind}' ("${tok.text}") ` +
                `at line ${tok.startPos.row + 1}, col ${tok.startPos.column + 1} ` +
                `(offset ${tok.start}-${tok.end})`
            );
        }
        return this.advance();
    }

    /**
     * Peek at the token `offset` non-comment positions ahead of the current
     * position, without consuming any tokens.
     *
     * @param {number} offset  1 = one token ahead (default).
     *   If `offset` exceeds the remaining non-comment tokens, the EOF sentinel
     *   (the last token in `this.tokens`) is returned rather than throwing.
     *   Callers always use small, hardcoded offsets (1), so this is intentional
     *   behaviour, not an error condition.
     */
    peekAhead(offset = 1) {
        if (offset < 1) {
            throw new _ParseError(`peekAhead: offset must be >= 1, got ${offset}`);
        }
        let count = 0;
        let i = this.pos;
        // First skip any pending-comment tokens at current pos
        while (
            i < this.tokens.length &&
            (this.tokens[i].kind === COMMENT_KINDS.LINE || this.tokens[i].kind === COMMENT_KINDS.BLOCK)
        ) {
            i++;
        }
        // Now find the Nth non-comment token beyond current
        while (i < this.tokens.length) {
            if (this.tokens[i].kind !== COMMENT_KINDS.LINE && this.tokens[i].kind !== COMMENT_KINDS.BLOCK) {
                if (count === offset) return this.tokens[i];
                count++;
            }
            i++;
        }
        return this.tokens[this.tokens.length - 1]; // eof
    }

    // ── Comment management ──────────────────────────────────────────────────

    /**
     * Flush all pending comment nodes as named children of `parent`.
     * Call this before adding any substantive child to a block node.
     */
    flushComments(parent) {
        // Clear this.pending *before* iterating so that any exception thrown
        // by _addChild does not leave stale comments to be re-flushed later.
        const pending = this.pending;
        this.pending = [];
        for (const c of pending) {
            parent._addChild(c);
        }
    }

    // ── Node factories ──────────────────────────────────────────────────────

    /** Create a CSTNode from a lexer token. */
    _tokNode(tok, type, isNamed = true) {
        return new CSTNode(type, tok.text, tok.start, tok.end, tok.startPos, tok.endPos, isNamed);
    }

    /** Create an anonymous (keyword/punctuation) token node. */
    _anonTok(tok) {
        return new CSTNode(tok.kind, tok.text, tok.start, tok.end, tok.startPos, tok.endPos, false);
    }

    /**
     * Build a named CSTNode spanning source[startIndex..endIndex].
     * text is sliced from source lazily once endIndex is known.
     */
    _node(type, startIndex, endIndex, startPosition, endPosition) {
        const text = this.source.slice(startIndex, endIndex);
        return new CSTNode(type, text, startIndex, endIndex, startPosition, endPosition, true);
    }

    /** Finalise a node's endIndex/endPosition/text after children are added. */
    _finalise(node, endTok) {
        node.endIndex = endTok.end;
        node.endPosition = endTok.endPos;
        node.text = this.source.slice(node.startIndex, node.endIndex);
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Grammar rules
    // ═══════════════════════════════════════════════════════════════════════

    // ── source_file ─────────────────────────────────────────────────────────

    parseSourceFile() {
        const eofTok = this.tokens[this.tokens.length - 1];
        const root = this._node(
            'source_file', 0, this.source.length,
            { row: 0, column: 0 }, eofTok.endPos
        );

        // Flush any leading comments (before package / first declaration).
        this.peek();
        this.flushComments(root);

        // Optional package declaration.
        if (this.peekKind() === 'package') {
            root._addChild(this.parsePackageDeclaration());
            this.peek();
            this.flushComments(root);
        }

        // Zero or more import clauses.
        while (this.peekKind() === 'import') {
            root._addChild(this.parseImportClause());
            this.peek();
            this.flushComments(root);
        }

        // Top-level declarations.
        while (this.peekKind() !== 'eof') {
            root._addChild(this.parseTopLevelDeclaration());
            this.peek();
            this.flushComments(root);
        }

        return root;
    }

    // ── Preamble ────────────────────────────────────────────────────────────

    parsePackageDeclaration() {
        const kw = this.expect('package');
        const id = this.expect('ident');
        const node = this._node('package_declaration', kw.start, id.end, kw.startPos, id.endPos);
        node._addChild(this._tokNode(id, 'identifier'), 'name');
        return node;
    }

    parseImportClause() {
        const kw = this.expect('import');
        const id = this.expect('ident');
        const node = this._node('import_clause', kw.start, id.end, kw.startPos, id.endPos);
        node._addChild(this._tokNode(id, 'identifier'), 'name');
        return node;
    }

    // ── Top-level declarations ──────────────────────────────────────────────

    parseTopLevelDeclaration() {
        const k = this.peekKind();
        const methodName = TOP_LEVEL_DISPATCH[k];
        if (!methodName) {
            throw new _ParseError(
                `Unexpected token '${k}' ("${this.peek().text}") ` +
                `at line ${this.peek().startPos.row + 1}`
            );
        }
        return this[methodName]();
    }

    // ── Enumeration declaration ─────────────────────────────────────────────

    parseEnumerationDeclaration() {
        const kw = this.expect('enum');
        const nameNode = this.parseDescribedName();
        this.expect('{');

        const node = this._node('enumeration_declaration', kw.start, 0, kw.startPos, null);
        node._addChild(nameNode, 'name');

        this.peek();
        this.flushComments(node);
        while (this.peekKind() !== '}') {
            node._addChild(this.parseEnumerationLiteral());
            this.peek();
            this.flushComments(node);
        }

        this._finalise(node, this.expect('}'));
        return node;
    }

    parseEnumerationLiteral() {
        const inner = this.parseDescribedName();
        const node = this._node('enumeration_literal', inner.startIndex, inner.endIndex,
            inner.startPosition, inner.endPosition);
        node._addChild(inner);
        return node;
    }

    // ── Tuple declaration ───────────────────────────────────────────────────

    parseTupleDeclaration() {
        const kw = this.expect('tuple');
        const nameNode = this.parseDescribedName();
        this.expect('{');

        const node = this._node('tuple_declaration', kw.start, 0, kw.startPos, null);
        node._addChild(nameNode, 'name');

        this.peek();
        this.flushComments(node);
        while (this.peekKind() !== '}') {
            if (this.peekKind() === 'separator') {
                node._addChild(this.parseSeparatorDeclaration());
            } else {
                node._addChild(this.parseFieldDeclaration());
            }
            this.peek();
            this.flushComments(node);
        }

        this._finalise(node, this.expect('}'));
        return node;
    }

    parseFieldDeclaration() {
        const nameNode = this.parseDescribedName();

        let optTok = null;
        if (this.peekKind() === 'optional') {
            optTok = this.advance();
        }

        const typeNode = this.parseTypeExpression();
        const endIdx = typeNode.endIndex;
        const endPos = typeNode.endPosition;

        const node = this._node('field_declaration', nameNode.startIndex, endIdx,
            nameNode.startPosition, endPos);
        node._addChild(nameNode, 'name');
        if (optTok) {
            // Registered under the 'optional' field name so the printer can
            // query it via node.childForFieldName('optional') rather than
            // scanning node.children for a matching text value.
            node._addChild(new CSTNode('optional', 'optional',
                optTok.start, optTok.end, optTok.startPos, optTok.endPos, false), 'optional');
        }
        node._addChild(typeNode, 'type');
        return node;
    }

    parseSeparatorDeclaration() {
        const kw = this.expect('separator');
        const symNode = this.parseSeparatorSymbol();
        const node = this._node('separator_declaration', kw.start, symNode.endIndex,
            kw.startPos, symNode.endPosition);
        node._addChild(symNode);
        return node;
    }

    parseSeparatorSymbol() {
        const tok = this.peek();
        if (tok.kind === 'ident' || SEPARATOR_SYMBOLS.has(tok.kind)) {
            this.advance();
            return this._tokNode(tok, 'separator_symbol');
        }
        throw new _ParseError(
            `Expected separator symbol (@, :, ; or identifier) but got '${tok.kind}' ` +
            `at line ${tok.startPos.row + 1}`
        );
    }

    // ── Record (type) declaration ───────────────────────────────────────────

    parseRecordDeclaration() {
        const startTok = this.peek();

        let qualNode = null;
        if (this.peekKind() === 'abstract' || this.peekKind() === 'final') {
            const qt = this.advance();
            qualNode = this._node('inheritance_qualifier', qt.start, qt.end, qt.startPos, qt.endPos);
        }

        this.expect('type');
        const nameNode = this.parseDescribedName();

        let parentNode = null;
        if (this.peekKind() === 'extends') {
            this.advance(); // consume 'extends'
            parentNode = this.parseQualifiedName();
        }

        this.expect('{');

        const node = this._node('record_declaration', startTok.start, 0, startTok.startPos, null);
        if (qualNode) node._addChild(qualNode);
        node._addChild(nameNode, 'name');
        if (parentNode) node._addChild(parentNode, 'parent');

        this.peek();
        this.flushComments(node);
        while (this.peekKind() !== '}') {
            if (this.peekKind() === 'freeze') {
                node._addChild(this.parseComponentFreezing());
            } else {
                node._addChild(this.parseComponentDeclaration());
            }
            this.peek();
            this.flushComments(node);
        }

        this._finalise(node, this.expect('}'));
        return node;
    }

    parseComponentDeclaration() {
        const nameNode = this.parseDescribedName();

        let optTok = null;
        if (this.peekKind() === 'optional') {
            optTok = this.advance();
        }

        const typeNode = this.parseTypeExpression();

        // Optional array_declaration: [lower .. upper]
        let arrayNode = null;
        if (this.peekKind() === '[') {
            arrayNode = this.parseArrayDeclaration();
        }

        const endNode = arrayNode ?? typeNode;
        const node = this._node('component_declaration', nameNode.startIndex, endNode.endIndex,
            nameNode.startPosition, endNode.endPosition);
        node._addChild(nameNode, 'name');
        if (optTok) {
            // Registered under the 'optional' field name; see the matching
            // comment in parseFieldDeclaration() above.
            node._addChild(new CSTNode('optional', 'optional',
                optTok.start, optTok.end, optTok.startPos, optTok.endPos, false), 'optional');
        }
        node._addChild(typeNode, 'type');
        if (arrayNode) node._addChild(arrayNode);
        return node;
    }

    parseArrayDeclaration() {
        const lb = this.expect('[');
        const lowerTok = this.expect('integer');
        const lowerNode = this._tokNode(lowerTok, 'integer');
        this.expect('..');

        let upperNode;
        if (this.peekKind() === '*') {
            const st = this.advance();
            // '*' is an anonymous (unnamed) node; the printer uses .text on it
            upperNode = new CSTNode('*', '*', st.start, st.end, st.startPos, st.endPos, false);
        } else {
            const ut = this.expect('integer');
            upperNode = this._tokNode(ut, 'integer');
        }

        const rb = this.expect(']');
        const node = this._node('array_declaration', lb.start, rb.end, lb.startPos, rb.endPos);
        node._addChild(lowerNode, 'lower');
        node._addChild(upperNode, 'upper');
        return node;
    }

    parseComponentFreezing() {
        const kw = this.expect('freeze');
        const compTok = this.expect('ident');
        const compNode = this._tokNode(compTok, 'identifier');
        this.expect('=');
        const valueNode = this.parseValue();

        const node = this._node('component_freezing', kw.start, valueNode.endIndex,
            kw.startPos, valueNode.endPosition);
        node._addChild(compNode, 'component');
        node._addChild(valueNode, 'value');
        return node;
    }

    // ── Check block ─────────────────────────────────────────────────────────

    parseCheckBlock() {
        const kw = this.expect('checks');
        const targetTok = this.expect('ident');
        const targetNode = this._tokNode(targetTok, 'identifier');
        this.expect('{');

        const node = this._node('check_block', kw.start, 0, kw.startPos, null);
        node._addChild(targetNode, 'target');

        this.peek();
        this.flushComments(node);
        while (this.peekKind() !== '}') {
            node._addChild(this.parseCheckDeclaration());
            this.peek();
            this.flushComments(node);
        }

        this._finalise(node, this.expect('}'));
        return node;
    }

    parseCheckDeclaration() {
        const exprNode = this.parseExpression(0);
        this.expect(',');

        // Optional severity keyword
        let severityNode = null;
        const sk = this.peekKind();
        if (sk === 'warning' || sk === 'error' || sk === 'fatal') {
            const st = this.advance();
            severityNode = this._node('severity', st.start, st.end, st.startPos, st.endPos);
        }

        // Required message string
        const messageNode = this.parseStringValue();

        // Optional details string and/or category identifier
        let detailsNode = null;
        let categoryNode = null;

        if (this.peekKind() === ',') {
            this.advance(); // consume ','
            const nk = this.peekKind();
            if (nk === 'string_double' || nk === 'string_triple_double' || nk === 'string_triple_single') {
                detailsNode = this.parseStringValue();
                if (this.peekKind() === ',') {
                    this.advance(); // consume ','
                    const ct = this.expect('ident');
                    categoryNode = this._tokNode(ct, 'identifier');
                }
            } else if (nk === 'ident') {
                const ct = this.advance();
                categoryNode = this._tokNode(ct, 'identifier');
            } else {
                // Per the LRM grammar, a ',' after the message can only be
                // followed by STRING_details or IDENTIFIER_component_name.
                // Anything else means the input doesn't match check_declaration;
                // surface a parse error (parseTrlc() falls back to leaving the
                // file verbatim) instead of silently discarding the ','.
                const bad = this.peek();
                throw new _ParseError(
                    `Expected a details string or category identifier after ',' ` +
                    `in check declaration, but got '${bad.kind}' ("${bad.text}") ` +
                    `at line ${bad.startPos.row + 1}, col ${bad.startPos.column + 1}`
                );
            }
        }

        const endNode = categoryNode ?? detailsNode ?? messageNode;
        const node = this._node('check_declaration',
            exprNode.startIndex, endNode.endIndex,
            exprNode.startPosition, endNode.endPosition);
        node._addChild(exprNode);
        if (severityNode) node._addChild(severityNode);
        node._addChild(messageNode, 'message');
        if (detailsNode) node._addChild(detailsNode, 'details');
        if (categoryNode) node._addChild(categoryNode, 'category');
        return node;
    }

    // ── Section declaration ─────────────────────────────────────────────────

    parseSectionDeclaration() {
        const kw = this.expect('section');
        const nameNode = this.parseStringValue();
        this.expect('{');

        const node = this._node('section_declaration', kw.start, 0, kw.startPos, null);
        node._addChild(nameNode, 'name');

        this.peek();
        this.flushComments(node);
        while (this.peekKind() !== '}') {
            if (this.peekKind() === 'section') {
                node._addChild(this.parseSectionDeclaration());
            } else {
                node._addChild(this.parseRecordObjectDeclaration());
            }
            this.peek();
            this.flushComments(node);
        }

        this._finalise(node, this.expect('}'));
        return node;
    }

    // ── Record object declaration ───────────────────────────────────────────

    parseRecordObjectDeclaration() {
        const typeNode = this.parseQualifiedName();
        const nameTok = this.expect('ident');
        const nameNode = this._tokNode(nameTok, 'identifier');
        this.expect('{');

        const node = this._node('record_object_declaration',
            typeNode.startIndex, 0, typeNode.startPosition, null);
        node._addChild(typeNode, 'type');
        node._addChild(nameNode, 'name');

        this.peek();
        this.flushComments(node);
        while (this.peekKind() !== '}') {
            node._addChild(this.parseFieldAssignment());
            this.peek();
            this.flushComments(node);
        }

        this._finalise(node, this.expect('}'));
        return node;
    }

    parseFieldAssignment() {
        const nameTok = this.expect('ident');
        const nameNode = this._tokNode(nameTok, 'identifier');
        this.expect('=');
        const valueNode = this.parseValue();

        const node = this._node('field_assignment',
            nameTok.start, valueNode.endIndex, nameTok.startPos, valueNode.endPosition);
        node._addChild(nameNode, 'name');
        node._addChild(valueNode, 'value');
        return node;
    }

    // ── Values ──────────────────────────────────────────────────────────────

    /**
     * Parse a _value: expression, array_value, or tuple_value.
     * After parsing the primary value, check for a separator-tuple continuation.
     */
    parseValue() {
        // Array value: [ elem, … ]
        if (this.peekKind() === '[') {
            const av = this.parseArrayValue();
            return this._trySeparatorContinuation(av);
        }

        // Parenthesised form: could be conditional, quantified, tuple_value,
        // or parenthesised_expression.  Dispatch by lookahead.
        if (this.peekKind() === '(') {
            const afterParen = this.peekAhead(1);
            if (afterParen.kind === 'if') {
                return this.parseConditionalExpression();
            }
            if (afterParen.kind === 'forall' || afterParen.kind === 'exists') {
                return this.parseQuantifiedExpression();
            }
            return this.parseParenthesisedOrTupleValue();
        }

        // Fall through to expression; check for separator continuation.
        const expr = this.parseExpression(0);
        return this._trySeparatorContinuation(expr);
    }

    parseArrayValue() {
        const lb = this.expect('[');
        const node = this._node('array_value', lb.start, 0, lb.startPos, null);

        if (this.peekKind() !== ']') {
            node._addChild(this.parseValue());
            while (this.peekKind() === ',') {
                this.advance(); // consume ','
                if (this.peekKind() === ']') break; // trailing comma
                node._addChild(this.parseValue());
            }
        }

        this._finalise(node, this.expect(']'));
        return node;
    }

    /**
     * Parse either a parenthesised expression or a parenthesised tuple value.
     * Disambiguation: if a comma follows the first element, it is a tuple.
     */
    parseParenthesisedOrTupleValue() {
        const lp = this.expect('(');

        // Empty tuple: ()
        if (this.peekKind() === ')') {
            const rp = this.advance();
            return this._node('tuple_value', lp.start, rp.end, lp.startPos, rp.endPos);
        }

        const first = this.parseValue();

        if (this.peekKind() === ',') {
            // Parenthesised tuple_value: ( val { , val } )
            const node = this._node('tuple_value', lp.start, 0, lp.startPos, null);
            node._addChild(first);
            while (this.peekKind() === ',') {
                this.advance(); // consume ','
                if (this.peekKind() === ')') break; // trailing comma
                node._addChild(this.parseValue());
            }
            this._finalise(node, this.expect(')'));
            return node;
        }

        // parenthesized_expression: ( expr )
        const rp = this.expect(')');
        const node = this._node('parenthesized_expression',
            lp.start, rp.end, lp.startPos, rp.endPos);
        node._addChild(first);
        return node;
    }

    /**
     * If the next token is a separator symbol (@, :, ;), wrap `left` into a
     * separated_tuple_value and then a tuple_value.  Otherwise return `left`.
     */
    _trySeparatorContinuation(left) {
        const k = this.peekKind();
        if (!SEPARATOR_SYMBOLS.has(k)) return left;

        // Build separated_tuple_value
        const stv = this._node('separated_tuple_value',
            left.startIndex, 0, left.startPosition, null);
        stv._addChild(left);

        while (SEPARATOR_SYMBOLS.has(this.peekKind())) {
            const sepTok = this.advance();
            stv._addChild(this._anonTok(sepTok)); // anonymous separator token

            // _separator_element = expression | array_value (NOT another tuple_value)
            const elem = (this.peekKind() === '[')
                ? this.parseArrayValue()
                : this.parseExpression(0);
            stv._addChild(elem);
        }

        const lastChild = stv.children[stv.children.length - 1];
        stv.endIndex = lastChild.endIndex;
        stv.endPosition = lastChild.endPosition;
        stv.text = this.source.slice(stv.startIndex, stv.endIndex);

        // Wrap in tuple_value
        const tv = this._node('tuple_value',
            stv.startIndex, stv.endIndex, stv.startPosition, stv.endPosition);
        tv._addChild(stv);
        return tv;
    }

    // ── Expression parsing (Pratt) ──────────────────────────────────────────

    /**
     * Parse an expression with minimum binding power `minBp`.
     * Stops when the next infix operator's lbp ≤ minBp.
     *
     * Delegates each postfix operator ('not in', member access, call, index)
     * to its own helper so this loop only holds the generic Pratt dispatch;
     * see _tryNotIn()/_tryPostfixOperator() below.
     */
    parseExpression(minBp) {
        this._exprDepth++;
        if (this._exprDepth > MAX_EXPRESSION_DEPTH) {
            throw new _ParseError(
                `Expression nesting exceeds maximum depth of ${MAX_EXPRESSION_DEPTH}`
            );
        }
        try {
            let left = this._parseUnaryOrPrimary();

            while (true) {
                const tok = this.peek();
                const k = tok.kind;

                if (k === 'not') {
                    const result = this._tryNotIn(left, minBp);
                    if (result === _Parser.STOP) break;
                    left = result;
                    continue;
                }

                const postfix = this._tryPostfixOperator(k, left, minBp);
                if (postfix !== null) {
                    left = postfix;
                    continue;
                }

                // ── Regular binary operators ─────────────────────────────────
                const bp = INFIX_BP[k];
                if (bp === undefined || bp <= minBp) break;

                const opTok = this.advance();
                // '**' is right-associative: right operand uses rbp = lbp - 1.
                const rbp = (k === '**') ? bp - 1 : bp;
                const right = this.parseExpression(rbp);

                const node = this._node('binary_expression',
                    left.startIndex, right.endIndex, left.startPosition, right.endPosition);
                node._addChild(left);
                node._addChild(this._anonTok(opTok));
                node._addChild(right);
                left = node;
            }

            return left;
        } finally {
            this._exprDepth--;
        }
    }

    /**
     * Handle a 'not' token in infix position: either build a 'not in'
     * binary_expression, or signal that the loop in parseExpression() should
     * stop (standalone 'not' is not valid in infix position, and a 'not in'
     * whose precedence is too low for the caller must also stop there).
     *
     * @returns {CSTNode | typeof _Parser.STOP}
     */
    _tryNotIn(left, minBp) {
        const afterNot = this.peekAhead(1);
        if (afterNot.kind !== 'in') return _Parser.STOP;

        const bp = INFIX_BP['in']; // same precedence as 'in'
        if (bp <= minBp) return _Parser.STOP;

        const notTok = this.advance();
        const inTok = this.advance();
        // 'not in' is left-associative (same as 'in'):
        //   x not in S not in T  →  (x not in S) not in T
        // Pass `bp` (not `bp - 1`) so the right operand stops before another
        // same-precedence operator, matching the tree-sitter grammar's
        // left-associative 'in'/'not in'.
        const right = this.parseExpression(bp); // left-associative
        const node = this._node('binary_expression',
            left.startIndex, right.endIndex, left.startPosition, right.endPosition);
        node._addChild(left);
        node._addChild(this._anonTok(notTok));
        node._addChild(this._anonTok(inTok));
        node._addChild(right);
        return node;
    }

    /**
     * Try to extend `left` with a postfix operator ('.', '(', '['). Returns
     * the new node, or null if `k` isn't a postfix operator, or if its
     * binding power is not greater than `minBp` (in which case the caller's
     * generic INFIX_BP fallback will also see bp <= minBp and stop the loop).
     */
    _tryPostfixOperator(k, left, minBp) {
        switch (k) {
            case '.': return this._parseMemberAccess(left, minBp);
            case '(': return this._parseCallExpression(left, minBp);
            case '[': return this._parseIndexExpression(left, minBp);
            default: return null;
        }
    }

    /** Member access: expr . identifier */
    _parseMemberAccess(left, minBp) {
        const bp = INFIX_BP['.'];
        if (bp <= minBp) return null;
        const dotTok = this.advance();
        const memberTok = this.expect('ident');
        const memberNode = this._tokNode(memberTok, 'identifier');
        const node = this._node('member_expression',
            left.startIndex, memberNode.endIndex, left.startPosition, memberNode.endPosition);
        node._addChild(left);
        node._addChild(this._anonTok(dotTok));
        node._addChild(memberNode, 'member');
        return node;
    }

    /** Function call: expr ( args ) */
    _parseCallExpression(left, minBp) {
        const bp = INFIX_BP['('];
        if (bp <= minBp) return null;
        const lp = this.advance();
        let argsNode = null;
        if (this.peekKind() !== ')') {
            argsNode = this._parseArgumentList();
        }
        const rp = this.expect(')');
        const node = this._node('call_expression',
            left.startIndex, rp.end, left.startPosition, rp.endPos);
        node._addChild(left, 'function');
        if (argsNode) node._addChild(argsNode, 'arguments');
        return node;
    }

    /** Array index: expr [ index ] */
    _parseIndexExpression(left, minBp) {
        const bp = INFIX_BP['['];
        if (bp <= minBp) return null;
        const lb = this.advance();
        const indexExpr = this.parseExpression(0);
        const rb = this.expect(']');
        const node = this._node('index_expression',
            left.startIndex, rb.end, left.startPosition, rb.endPos);
        node._addChild(left, 'object');
        node._addChild(indexExpr, 'index');
        return node;
    }

    _parseUnaryOrPrimary() {
        const k = this.peekKind();

        // Unary prefix operators: not, -, +, abs  (tree-sitter prec = 8)
        if (k === 'not' || k === '-' || k === '+' || k === 'abs') {
            const opTok = this.advance();
            const operand = this.parseExpression(UNARY_BINDING_POWER);
            const node = this._node('unary_expression',
                opTok.start, operand.endIndex, opTok.startPos, operand.endPosition);
            node._addChild(this._anonTok(opTok)); // anonymous operator token
            node._addChild(operand);
            return node;
        }

        return this._parsePrimary();
    }

    _parsePrimary() {
        const tok = this.peek();
        const k = tok.kind;

        // ── Parenthesised: conditional, quantified, or expr ──────────────────
        if (k === '(') {
            const afterParen = this.peekAhead(1);
            if (afterParen.kind === 'if') {
                return this.parseConditionalExpression();
            }
            if (afterParen.kind === 'forall' || afterParen.kind === 'exists') {
                return this.parseQuantifiedExpression();
            }
            const lp = this.advance();
            const expr = this.parseExpression(0);
            const rp = this.expect(')');
            const node = this._node('parenthesized_expression',
                lp.start, rp.end, lp.startPos, rp.endPos);
            node._addChild(expr);
            return node;
        }

        // ── Integer literal ───────────────────────────────────────────────────
        if (k === 'integer') {
            this.advance();
            return this._tokNode(tok, 'integer');
        }

        // ── Decimal literal ───────────────────────────────────────────────────
        if (k === 'decimal') {
            this.advance();
            return this._tokNode(tok, 'decimal');
        }

        // ── String literals ───────────────────────────────────────────────────
        if (k === 'string_double' || k === 'string_triple_double' || k === 'string_triple_single') {
            this.advance();
            return this._buildStringNode(tok);
        }

        // ── Boolean ───────────────────────────────────────────────────────────
        if (k === 'true' || k === 'false') {
            this.advance();
            return this._node('boolean', tok.start, tok.end, tok.startPos, tok.endPos);
        }

        // ── Null ──────────────────────────────────────────────────────────────
        if (k === 'null') {
            this.advance();
            return this._node('null', tok.start, tok.end, tok.startPos, tok.endPos);
        }

        // ── Identifier / qualified_name ───────────────────────────────────────
        // In expression context an identifier is the start of a qualified_name.
        // Builtin type names (Boolean, Integer, …) are lexed as 'ident' tokens
        // and are therefore already handled by the k === 'ident' branch.
        if (k === 'ident') {
            this.advance();
            return this._node('qualified_name', tok.start, tok.end, tok.startPos, tok.endPos);
        }

        throw new _ParseError(
            `Unexpected token '${k}' ("${tok.text}") in expression ` +
            `at line ${tok.startPos.row + 1}`
        );
    }

    // ── Conditional expression: (if cond then val elsif … else val) ──────────

    parseConditionalExpression() {
        const lp = this.expect('(');
        this.expect('if');
        const cond = this.parseExpression(0);
        this.expect('then');
        const thenExpr = this.parseExpression(0);

        const node = this._node('conditional_expression', lp.start, 0, lp.startPos, null);
        node._addChild(cond, 'condition');
        node._addChild(thenExpr, 'then');

        while (this.peekKind() === 'elsif') {
            this.advance(); // consume 'elsif'
            const ec = this.parseExpression(0);
            this.expect('then');
            const et = this.parseExpression(0);
            node._addChild(ec, 'elsif_condition');
            node._addChild(et, 'elsif_then');
        }

        this.expect('else');
        const elseExpr = this.parseExpression(0);
        node._addChild(elseExpr, 'else');

        this._finalise(node, this.expect(')'));
        return node;
    }

    // ── Quantified expression: (forall|exists var in src => body) ────────────

    parseQuantifiedExpression() {
        const lp = this.expect('(');
        const quantTok = this.advance(); // 'forall' or 'exists'
        const varTok = this.expect('ident');
        const varNode = this._tokNode(varTok, 'identifier');
        const inTok = this.expect('in');
        const srcExpr = this.parseExpression(0);
        const arrowTok = this.expect('=>');
        const bodyExpr = this.parseExpression(0);
        const rp = this.expect(')');

        const node = this._node('quantified_expression',
            lp.start, rp.end, lp.startPos, rp.endPos);

        // The printer locates the forall/exists keyword via the single anonymous
        // child.  The surrounding punctuation ('(', 'in', '=>', ')') is hardcoded
        // as string literals in the printer and not stored in the CST.
        node._addChild(this._anonTok(quantTok)); // anonymous: 'forall' or 'exists'
        node._addChild(varNode, 'variable');
        node._addChild(srcExpr, 'source');
        node._addChild(bodyExpr, 'body');
        return node;
    }

    // ── Argument list ─────────────────────────────────────────────────────────

    _parseArgumentList() {
        const first = this.parseExpression(0);
        const node = this._node('argument_list',
            first.startIndex, 0, first.startPosition, null);
        node._addChild(first);

        while (this.peekKind() === ',') {
            this.advance(); // consume ','
            if (this.peekKind() === ')') break; // guard against trailing comma
            node._addChild(this.parseExpression(0));
        }

        const last = node.namedChildren[node.namedChildren.length - 1];
        node.endIndex = last.endIndex;
        node.endPosition = last.endPosition;
        node.text = this.source.slice(node.startIndex, node.endIndex);
        return node;
    }

    // ── Type expressions (field / component declarations) ────────────────────

    /**
     * Parse a type expression: builtin_type, qualified_name, or union_type.
     * Called in field/component declaration context (NOT expression context).
     */
    parseTypeExpression() {
        if (this.peekKind() === '[') {
            return this.parseUnionType();
        }
        return this._parseTypeNameOrBuiltin();
    }

    _parseTypeNameOrBuiltin() {
        const tok = this.peek();
        if (tok.kind !== 'ident') {
            throw new _ParseError(
                `Expected type name but got '${tok.kind}' ("${tok.text}") ` +
                `at line ${tok.startPos.row + 1}`
            );
        }
        this.advance();
        if (BUILTIN_TYPES.has(tok.text)) {
            return this._node('builtin_type', tok.start, tok.end, tok.startPos, tok.endPos);
        }
        // Parse qualified_name: already consumed first identifier, maybe more .id segments.
        return this._extendQualifiedName(tok);
    }

    parseUnionType() {
        const lb = this.expect('[');
        const node = this._node('union_type', lb.start, 0, lb.startPos, null);
        node._addChild(this.parseQualifiedName());

        while (this.peekKind() === ',') {
            this.advance(); // consume ','
            if (this.peekKind() === ']') break; // guard
            node._addChild(this.parseQualifiedName());
        }

        this._finalise(node, this.expect(']'));
        return node;
    }

    /**
     * Parse a qualified_name: identifier ('.' identifier)*.
     * Used in: record-object type, extends clause, union_type members.
     */
    parseQualifiedName() {
        const first = this.expect('ident');
        return this._extendQualifiedName(first);
    }

    /**
     * Given the already-consumed first identifier token `firstTok`, consume
     * any trailing '.identifier' segments and build a qualified_name node.
     */
    _extendQualifiedName(firstTok) {
        let endIdx = firstTok.end;
        let endPos = firstTok.endPos;

        while (this.peekKind() === '.') {
            // Lookahead: only consume if followed by an identifier (not '..' or EOF).
            const afterDot = this.peekAhead(1);
            if (afterDot.kind !== 'ident') break;
            this.advance(); // consume '.'
            const idTok = this.advance(); // consume identifier
            endIdx = idTok.end;
            endPos = idTok.endPos;
        }

        return this._node('qualified_name', firstTok.start, endIdx, firstTok.startPos, endPos);
    }

    // ── Described name ────────────────────────────────────────────────────────

    /**
     * Parse a described_name: identifier [ string ]
     * Used for enum/tuple/record/component/field names.
     */
    parseDescribedName() {
        const idTok = this.expect('ident');
        const idNode = this._tokNode(idTok, 'identifier');

        const node = this._node('described_name',
            idTok.start, idTok.end, idTok.startPos, idTok.endPos);
        node._addChild(idNode, 'name');

        // Optional description string
        const nk = this.peekKind();
        if (nk === 'string_double' || nk === 'string_triple_double' || nk === 'string_triple_single') {
            const strTok = this.advance();
            const strNode = this._buildStringNode(strTok);
            node._addChild(strNode, 'description');
            node.endIndex = strNode.endIndex;
            node.endPosition = strNode.endPosition;
            node.text = this.source.slice(node.startIndex, node.endIndex);
        }

        return node;
    }

    // ── String value ──────────────────────────────────────────────────────────

    /**
     * Expect and consume a string token, returning a `string` CSTNode wrapping
     * the specific string-type inner node.
     */
    parseStringValue() {
        const k = this.peekKind();
        if (k !== 'string_double' && k !== 'string_triple_double' && k !== 'string_triple_single') {
            throw new _ParseError(
                `Expected string but got '${k}' at line ${this.peek().startPos.row + 1}`
            );
        }
        return this._buildStringNode(this.advance());
    }

    /**
     * Build a `string` node (wrapping the specific kind) from a string token.
     * The printer dispatches on the `string` type and delegates to the inner
     * type node, so we always create a two-level structure.
     */
    _buildStringNode(tok) {
        const innerType =
            tok.kind === 'string_double' ? 'double_quoted_string' :
                tok.kind === 'string_triple_double' ? 'triple_double_quoted_string' :
                    'triple_single_quoted_string';
        const inner = this._tokNode(tok, innerType);
        const outer = this._node('string', tok.start, tok.end, tok.startPos, tok.endPos);
        outer._addChild(inner);
        return outer;
    }
}
