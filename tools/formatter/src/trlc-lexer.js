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

// Tokenizer for TRLC/RSL source files.
//
// Produces a flat array of Token objects. Whitespace is consumed silently;
// comments are emitted as tokens so the parser can attach them to the CST.
//
// Token shape:
//   { kind, text, start, end, startPos, endPos }
//   kind     — see KEYWORDS set below, or one of the literal strings for
//              operators/punctuation, or 'ident'/'integer'/'decimal'/
//              'string_double'/'string_triple_double'/'string_triple_single'/
//              'line_comment'/'block_comment'/'eof'
//   text     — raw source text
//   start    — byte offset of first character
//   end      — byte offset one past last character
//   startPos — { row, column } (0-based)
//   endPos   — { row, column } (0-based, at the character AFTER the last one)

// Every reserved word in TRLC. These are returned as tokens whose kind equals
// their text (e.g. kind = 'package', kind = 'not').
// Exported so consumers (e.g. the parser) can reference the grammar's keyword
// set instead of re-deriving it; the parser's own literal comparisons
// (e.g. peekKind() === 'package') are checks against token kinds produced
// from this same set, not a second, independently-maintained list.
export const KEYWORDS = new Set([
    'package', 'import',
    'type', 'enum', 'tuple', 'checks', 'section',
    'freeze', 'extends', 'abstract', 'final', 'optional', 'separator',
    'warning', 'error', 'fatal',
    'and', 'or', 'not', 'xor', 'implies', 'in',
    'forall', 'exists', 'abs',
    'if', 'then', 'elsif', 'else',
    'true', 'false', 'null',
]);

// Single source of truth for comment token kinds. Shared with the parser
// (comment skipping/attachment in trlc-parser-impl.js) and the printer
// (COMMENT_TYPES in printer.js) so the two token kinds only need to be
// spelled out once.
export const COMMENT_KINDS = Object.freeze({
    LINE: 'line_comment',
    BLOCK: 'block_comment',
});

// Unicode character class tests for identifier lexing.
// TRLC identifiers start with a Unicode letter or underscore, and continue
// with Unicode letters, decimal digits, or underscores.
const RE_IDENT_START = /[\p{L}_]/u;
const RE_IDENT_CONT = /[\p{L}\p{Nd}_]/u;

// Single-character operator and punctuation tokens.  Stored as a Set for O(1)
// membership testing inside the hot tokenizer loop.
const SINGLE_CHARS = new Set(['.', '+', '*', '/', '%', '<', '>', '(', ')', '{', '}', '[', ']', ',', ';', ':', '@', '=', '-']);

export class LexError extends Error {
    constructor(msg) {
        super(msg);
        this.name = 'LexError';
    }
}

/**
 * Tokenize a TRLC/RSL source string.
 *
 * @param {string} source
 * @returns {Array<{kind:string,text:string,start:number,end:number,startPos:{row:number,column:number},endPos:{row:number,column:number}}>}
 * @throws {LexError} on unterminated strings or other lex errors
 */
export function tokenize(source) {
    const tokens = [];
    let pos = 0;   // current byte offset into source
    let row = 0;   // 0-based line number
    let col = 0;   // 0-based column number

    function curPos() {
        return { row, column: col };
    }

    // Advance one character, updating row/col.
    function advance() {
        const ch = source[pos];
        if (ch === '\r') {
            if (source[pos + 1] === '\n') {
                pos += 2; // CRLF counts as one newline
            } else {
                pos += 1;
            }
            row++;
            col = 0;
        } else if (ch === '\n') {
            pos++;
            row++;
            col = 0;
        } else {
            pos++;
            col++;
        }
        return ch;
    }

    function peek(offset = 0) {
        return source[pos + offset];
    }

    function emit(kind, start, startPos) {
        tokens.push({ kind, text: source.slice(start, pos), start, end: pos, startPos, endPos: curPos() });
    }

    while (pos < source.length) {
        const ch = source[pos];

        // ── Whitespace ───────────────────────────────────────────────────────
        if (ch === ' ' || ch === '\t' || ch === '\r' || ch === '\n') {
            advance();
            continue;
        }

        const start = pos;
        const startPos = curPos();

        // ── Line comment: //... ──────────────────────────────────────────────
        if (ch === '/' && peek(1) === '/') {
            while (pos < source.length && source[pos] !== '\r' && source[pos] !== '\n') {
                advance();
            }
            emit(COMMENT_KINDS.LINE, start, startPos);
            continue;
        }

        // ── Block comment: /* ... */ ─────────────────────────────────────────
        if (ch === '/' && peek(1) === '*') {
            advance(); advance(); // consume /*
            let closed = false;
            while (pos < source.length) {
                if (source[pos] === '*' && peek(1) === '/') {
                    advance(); advance(); // consume */
                    closed = true;
                    break;
                }
                advance();
            }
            if (!closed) {
                throw new LexError(`Unterminated block comment starting at line ${startPos.row + 1}`);
            }
            emit(COMMENT_KINDS.BLOCK, start, startPos);
            continue;
        }

        // ── Triple double-quoted string: """...""" ────────────────────────────
        if (ch === '"' && peek(1) === '"' && peek(2) === '"') {
            advance(); advance(); advance(); // consume """
            let closed = false;
            while (pos < source.length) {
                if (source[pos] === '"' && peek(1) === '"' && peek(2) === '"') {
                    advance(); advance(); advance(); // consume """
                    closed = true;
                    break;
                }
                advance();
            }
            if (!closed) {
                throw new LexError(`Unterminated triple-double-quoted string at line ${startPos.row + 1}`);
            }
            emit('string_triple_double', start, startPos);
            continue;
        }

        // ── Double-quoted string: "..." (no embedded newlines) ───────────────
        if (ch === '"') {
            advance(); // consume opening "
            let closed = false;
            while (pos < source.length) {
                const c = source[pos];
                if (c === '"') {
                    advance(); // consume closing "
                    closed = true;
                    break;
                }
                if (c === '\n' || c === '\r') {
                    // Unterminated — surface as lex error so the parser
                    // returns hasError=true and the formatter passes through.
                    throw new LexError(`Unterminated string literal at line ${startPos.row + 1}`);
                }
                if (c === '\\') {
                    advance(); // skip backslash
                    if (pos < source.length) advance(); // skip escaped char
                } else {
                    advance();
                }
            }
            if (!closed) {
                throw new LexError(`Unterminated string literal at line ${startPos.row + 1}`);
            }
            emit('string_double', start, startPos);
            continue;
        }

        // ── Triple single-quoted string: '''...''' ────────────────────────────
        if (ch === "'" && peek(1) === "'" && peek(2) === "'") {
            advance(); advance(); advance(); // consume '''
            let closed = false;
            while (pos < source.length) {
                if (source[pos] === "'" && peek(1) === "'" && peek(2) === "'") {
                    advance(); advance(); advance(); // consume '''
                    closed = true;
                    break;
                }
                advance();
            }
            if (!closed) {
                throw new LexError(`Unterminated triple-single-quoted string at line ${startPos.row + 1}`);
            }
            emit('string_triple_single', start, startPos);
            continue;
        }

        // ── Numeric literals ─────────────────────────────────────────────────
        if (ch >= '0' && ch <= '9') {
            if (ch === '0' && (peek(1) === 'x' || peek(1) === 'X')) {
                // Hexadecimal: 0x[0-9a-fA-F_]+
                advance(); advance(); // consume 0x
                if (pos >= source.length || !/[0-9a-fA-F_]/.test(source[pos])) {
                    throw new LexError(`Expected hex digits after '0x' at line ${startPos.row + 1}`);
                }
                while (pos < source.length && /[0-9a-fA-F_]/.test(source[pos])) advance();
                emit('integer', start, startPos);
            } else if (ch === '0' && (peek(1) === 'b' || peek(1) === 'B')) {
                // Binary: 0b[01_]+
                advance(); advance(); // consume 0b
                if (pos >= source.length || !/[01_]/.test(source[pos])) {
                    throw new LexError(`Expected binary digits after '0b' at line ${startPos.row + 1}`);
                }
                while (pos < source.length && /[01_]/.test(source[pos])) advance();
                emit('integer', start, startPos);
            } else {
                // Decimal digits with optional _ separators
                while (pos < source.length && /[0-9_]/.test(source[pos])) advance();
                // Decimal number: digits '.' digits  (not '..' which is an operator)
                if (
                    pos < source.length &&
                    source[pos] === '.' &&
                    source[pos + 1] !== '.' &&
                    source[pos + 1] >= '0' && source[pos + 1] <= '9'
                ) {
                    advance(); // consume '.'
                    while (pos < source.length && /[0-9_]/.test(source[pos])) advance();
                    emit('decimal', start, startPos);
                } else {
                    emit('integer', start, startPos);
                }
            }
            continue;
        }

        // ── Identifiers and keywords ─────────────────────────────────────────
        if (RE_IDENT_START.test(ch)) {
            while (pos < source.length && RE_IDENT_CONT.test(source[pos])) advance();
            const text = source.slice(start, pos);
            const kind = KEYWORDS.has(text) ? text : 'ident';
            tokens.push({ kind, text, start, end: pos, startPos, endPos: curPos() });
            continue;
        }

        // ── Two-character operators (must be tried before single-char) ────────
        if (ch === '*' && peek(1) === '*') { advance(); advance(); emit('**', start, startPos); continue; }
        if (ch === '.' && peek(1) === '.') { advance(); advance(); emit('..', start, startPos); continue; }
        if (ch === '=' && peek(1) === '>') { advance(); advance(); emit('=>', start, startPos); continue; }
        if (ch === '=' && peek(1) === '=') { advance(); advance(); emit('==', start, startPos); continue; }
        if (ch === '!' && peek(1) === '=') { advance(); advance(); emit('!=', start, startPos); continue; }
        if (ch === '<' && peek(1) === '=') { advance(); advance(); emit('<=', start, startPos); continue; }
        if (ch === '>' && peek(1) === '=') { advance(); advance(); emit('>=', start, startPos); continue; }

        // ── Single-character tokens ───────────────────────────────────────────
        if (SINGLE_CHARS.has(ch)) {
            advance();
            emit(ch, start, startPos);
            continue;
        }

        throw new LexError(
            `Unexpected character '${ch}' (U+${ch.codePointAt(0).toString(16).padStart(4, '0')}) ` +
            `at line ${startPos.row + 1}, column ${startPos.column + 1}`
        );
    }

    // Always end with an EOF sentinel token.
    const eofPos = curPos();
    tokens.push({ kind: 'eof', text: '', start: pos, end: pos, startPos: eofPos, endPos: eofPos });
    return tokens;
}
