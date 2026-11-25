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

import { parseTrlc } from "./trlc-parser-impl.js";

export const parsers = {
    trlc: {
        parse(text) {
            if (typeof text !== "string") {
                throw new TypeError(
                    `[trlc-parser] parse() expected a string but received ${typeof text}.`
                );
            }
            // Strip any BOM characters before parsing so the tokenizer never
            // sees a stray \uFEFF at position 0.  The printer's isDroppableError()
            // handles any zero-content ERROR nodes that remain after formatting.
            const clean = text.replace(/\uFEFF/g, "");
            return parseTrlc(clean);
        },
        astFormat: "trlc-ast",
        locStart: (node) => node.startIndex,
        locEnd: (node) => node.endIndex,
    },
};
