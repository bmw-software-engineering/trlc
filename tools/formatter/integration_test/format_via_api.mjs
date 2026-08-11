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

import { readFileSync } from "node:fs";
import prettier from "prettier";
import * as trlc from "../src/index.js";

const [, , inputPath, optionsPath] = process.argv;

if (!inputPath) {
    process.stderr.write("Usage: format_via_api.mjs <input-file> [options-file]\n");
    process.exit(1);
}

let content;
try {
    content = readFileSync(inputPath, "utf8");
} catch (err) {
    process.stderr.write(`format_via_api: cannot read "${inputPath}": ${err.message}\n`);
    process.exit(1);
}

let extraOptions = {};
if (optionsPath) {
    try {
        extraOptions = JSON.parse(readFileSync(optionsPath, "utf8"));
    } catch (err) {
        process.stderr.write(`format_via_api: cannot read options "${optionsPath}": ${err.message}\n`);
        process.exit(1);
    }
}

let formatted;
try {
    formatted = await prettier.format(content, {
        plugins: [trlc],
        parser: "trlc",
        filepath: inputPath,
        tabWidth: 4,
        ...extraOptions,
    });
} catch (err) {
    process.stderr.write(`format_via_api: formatting failed for "${inputPath}": ${err.message}\n`);
    process.exit(1);
}

if (typeof formatted !== "string") {
    process.stderr.write(
        `format_via_api: prettier.format() returned ${typeof formatted} instead of a string for "${inputPath}"\n`,
    );
    process.exit(1);
}

process.stdout.write(formatted);
