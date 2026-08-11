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

// Register TRLC and RSL as Prettier-known languages
export const languages = [
    {
        name: "TRLC",
        parsers: ["trlc"],
        extensions: [".trlc", ".rsl"],
        // Both language IDs so editors that register "trlc" and "rsl" separately
        // both trigger the formatter without additional configuration.
        vscodeLanguageIds: ["trlc", "rsl"],
        tmScope: "source.trlc",
    },
];
