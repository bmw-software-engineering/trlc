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

// Default values used both by Prettier's option registration and by printer.js.
// Keeping them here avoids duplicating magic numbers across files.
export const DEFAULT_TAB_WIDTH = 4;
export const DEFAULT_ATTRIBUTE_GAP = 2;

// Custom Prettier options for TRLC formatting
export const options = {
    trlcNormalizeAttributes: {
        type: "boolean",
        default: true,
        description:
            "Apply R08 column alignment: align type tokens across all fields in a " +
            "type/tuple block to the same column (snapped to tabWidth). " +
            "Set to false to preserve source spacing verbatim.",
    },
    trlcAttributeGap: {
        type: "int",
        default: 2,
        description:
            "Minimum number of spaces between the longest field name and the type " +
            "column before snapping to the nearest tabWidth multiple (R08).",
        range: { start: 0, end: Infinity, step: 1 },
    },
    trlcSortImports: {
        type: "boolean",
        default: true,
        description:
            "Sort consecutive import statements alphabetically (case-insensitive). " +
            "TRLC import order is semantically neutral. Set to false to preserve " +
            "source order.",
    },
};
