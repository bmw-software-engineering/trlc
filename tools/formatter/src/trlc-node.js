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

// CSTNode — mirrors the tree-sitter SyntaxNode API surface used by printer.js.
//
// Required surface:
//   node.type              string  — node type name ("binary_expression", …)
//   node.text              string  — raw source text covered by this node
//   node.startIndex        number  — byte offset of first character
//   node.endIndex          number  — byte offset one past the last character
//   node.startPosition     {row,column}
//   node.endPosition       {row,column}
//   node.isNamed           boolean — named rule node vs anonymous token
//   node.hasError          boolean — set true on source_file when parse fails
//   node.children          CSTNode[] — all children (named + anonymous)
//   node.namedChildren     CSTNode[] — filtered: isNamed === true
//   node.childForFieldName(name)    → CSTNode | null
//   node.childrenForFieldName(name) → CSTNode[]   (for multi-valued fields)

export class CSTNode {
    constructor(type, text, startIndex, endIndex, startPosition, endPosition, isNamed = true) {
        this.type = type;
        this.text = text;
        this.startIndex = startIndex;
        this.endIndex = endIndex;
        this.startPosition = startPosition;
        this.endPosition = endPosition;
        this.isNamed = isNamed;
        this.hasError = false;
        /** @type {CSTNode[]} */
        this.children = [];
        /** @type {Map<string, CSTNode[]> | null} */
        this._fields = null;
    }

    /** All named children (isNamed === true). Computed on demand. */
    get namedChildren() {
        return this.children.filter((c) => c.isNamed);
    }

    /** Return the first child registered under the given field name, or null. */
    childForFieldName(name) {
        const arr = this._fields && this._fields.get(name);
        return arr && arr.length > 0 ? arr[0] : null;
    }

    /** Return all children registered under the given field name (may be empty). */
    childrenForFieldName(name) {
        return (this._fields && this._fields.get(name)) ?? [];
    }

    /**
     * Append a child to this node.
     * @param {CSTNode} child
     * @param {string|null} [fieldName] — register as a named field if supplied
     * @throws {TypeError} if `child` is not a CSTNode instance
     */
    _addChild(child, fieldName = null) {
        if (!(child instanceof CSTNode)) {
            throw new TypeError(
                `CSTNode._addChild: expected a CSTNode but received ${child === null ? "null" : typeof child
                }. This indicates a parser bug.`
            );
        }
        this.children.push(child);
        if (fieldName !== null) {
            if (!this._fields) this._fields = new Map();
            const arr = this._fields.get(fieldName);
            if (arr) {
                arr.push(child);
            } else {
                this._fields.set(fieldName, [child]);
            }
        }
        return this;
    }
}


