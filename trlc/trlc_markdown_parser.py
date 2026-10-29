#!/usr/bin/env python3
#
# TRLC - Treat Requirements Like Code
# Copyright (C) 2026 Bayerische Motoren Werke Aktiengesellschaft (BMW AG)
#
# This file is part of the TRLC Python Reference Implementation.
#
# TRLC is free software: you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# TRLC is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
# License for more details.
#
# You should have received a copy of the GNU General Public License
# along with TRLC. If not, see <https://www.gnu.org/licenses/>.

from trlc import ast
from trlc.errors import TRLC_Error
from trlc.parser import Parser


class TrlcMarkdownParser(Parser):
    """Parser for .trlc.md files.

    Reuses TRLC Parser logic for record/object/value semantics and only
    overrides markdown-specific preamble/section entry points.
    """

    # The H1 heading takes the role of the 'package' keyword, so the
    # inherited preamble parsing applies unchanged to markdown files.
    PACKAGE_KEYWORD = "#"

    # Markdown-friendly aliases that intentionally map to TRLC block tokens.
    MD_SECTION_START_TOKEN = "C_BRA"
    MD_SECTION_END_TOKEN = "C_KET"

    def __init__(
        self,
        mh,
        stab,
        file_name,
        lint_mode,
        error_recovery,
        primary_file=True,
        lexer=None,
    ):
        super().__init__(
            mh=mh,
            stab=stab,
            file_name=file_name,
            lint_mode=lint_mode,
            error_recovery=error_recovery,
            primary_file=primary_file,
            lexer=lexer,
        )
        if lexer is not None and hasattr(lexer, "KEYWORDS"):
            self.language_keywords = lexer.KEYWORDS

    def parse_preamble(self, kind):
        # markdown files are routed through TRLC flow in Source_Manager
        assert kind == "trlc"
        super().parse_preamble(kind)

    def parse_trlc_entry(self):
        self.cu.add_item(self.parse_record_object_declaration())

    def parse_trlc_file(self):
        assert self.cu.package is not None

        ok = True
        while self.peek("IDENTIFIER"):
            try:
                self.parse_trlc_entry()
            except TRLC_Error as err:
                if not self.error_recovery or err.kind == "lex error":
                    raise

                ok = False

                # Mirror TRLC recovery style: scan until likely new entry.
                self.skip_until_newline()
                while not self.peek_eof():
                    if not self.peek("IDENTIFIER"):
                        pass
                    elif self.stab.contains(self.nt.value):
                        n_sym = self.stab.lookup_assuming(self.mh, self.nt.value)
                        if isinstance(n_sym, ast.Package):
                            break
                    elif self.cu.package.symbols.contains(self.nt.value):
                        n_sym = self.cu.package.symbols.lookup_assuming(
                            self.mh, self.nt.value
                        )
                        if isinstance(n_sym, ast.Record_Type):
                            break
                    self.advance()
                    self.skip_until_newline()

        self.match_eof()

        for tok in self.lexer.tokens:
            if tok.kind == "COMMENT":
                self.cu.package.set_ast_link(tok)

        return ok
