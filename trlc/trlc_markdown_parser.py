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

        # H1: '# PackageName'
        self.match_kw("#")
        t_pkg = self.ct
        self.match("IDENTIFIER")

        declare_package = not self.stab.contains(self.ct.value)
        if declare_package:
            pkg = ast.Package(
                name=self.ct.value,
                location=self.ct.location,
                builtin_stab=self.stab,
                declared_late=True,
            )
            self.stab.register(self.mh, pkg)
        else:
            pkg = self.stab.lookup(self.mh, self.ct, ast.Package)

        pkg.set_ast_link(t_pkg)
        pkg.set_ast_link(self.ct)

        self.cu.set_package(pkg)
        self.default_scope.push(self.cu.package.symbols)

        # Optional import list right after H1
        while self.peek_kw("import"):
            self.match_kw("import")
            pkg.set_ast_link(self.ct)
            self.match("IDENTIFIER")
            self.cu.add_import(self.mh, self.ct)

    def parse_section_declaration(self):
        # H2: '## Section Name'
        self.match_kw("##")
        t_section = self.ct
        self.match("STRING")
        sec = ast.Section(
            name=self.ct.value,
            location=self.ct.location,
            parent=self.section[-1] if self.section else None,
        )
        sec.set_ast_link(self.ct)
        sec.set_ast_link(t_section)
        self.section.append(sec)

        self.match(self.MD_SECTION_START_TOKEN)
        sec.set_ast_link(self.ct)
        while not self.peek(self.MD_SECTION_END_TOKEN):
            self.parse_trlc_entry()
        self.match(self.MD_SECTION_END_TOKEN)
        sec.set_ast_link(self.ct)
        self.section.pop()

    def parse_trlc_entry(self):
        if self.peek_kw("##"):
            self.parse_section_declaration()
        else:
            self.cu.add_item(self.parse_record_object_declaration())

    def parse_trlc_file(self):
        assert self.cu.package is not None

        ok = True
        while self.peek_kw("##") or self.peek("IDENTIFIER"):
            try:
                self.parse_trlc_entry()
            except TRLC_Error as err:
                if not self.error_recovery or err.kind == "lex error":
                    raise

                ok = False

                # Mirror TRLC recovery style: scan until likely new entry.
                self.skip_until_newline()
                while not self.peek_eof():
                    if self.peek_kw("##"):
                        break
                    elif self.peek(self.MD_SECTION_END_TOKEN):
                        # Markdown lexer auto-emits section closing tokens.
                        # If we reached one during recovery, consume it to
                        # avoid a secondary "expected end-of-file" error.
                        self.advance()
                        break
                    elif not self.peek("IDENTIFIER"):
                        pass
                    elif self.stab.contains(self.nt.value):
                        n_sym = self.stab.lookup_assuming(self.mh, self.nt.value)
                        if isinstance(n_sym, ast.Package):
                            break
                    elif self.cu.package.symbols.contains(self.nt.value):
                        n_sym = self.cu.package.symbols.lookup_assuming(
                            self.mh, self.nt.value)
                        if isinstance(n_sym, ast.Record_Type):
                            break
                    self.advance()
                    self.skip_until_newline()

        # Markdown lexer emits section close tokens at EOF for open H2 blocks.
        # After recovery from earlier semantic errors, these can remain
        # unconsumed and otherwise surface as secondary EOF/brace errors.
        while self.peek(self.MD_SECTION_END_TOKEN):
            self.match(self.MD_SECTION_END_TOKEN)

        self.match_eof()

        for tok in self.lexer.tokens:
            if tok.kind == "COMMENT":
                self.cu.package.set_ast_link(tok)

        return ok
