#!/usr/bin/env python3
#
# TRLC - Treat Requirements Like Code
# Copyright (C) 2022-2023 Bayerische Motoren Werke Aktiengesellschaft (BMW AG)
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
from trlc.errors import Message_Handler, TRLC_Error
from trlc.vcg import VCG


class Linter:
    def __init__(self, mh, stab, verify_checks, debug_vcg, cvc5_binary):
        # lobster-exclude: Not safety relevant
        assert isinstance(mh, Message_Handler)
        assert isinstance(stab, ast.Symbol_Table)
        assert isinstance(verify_checks, bool)
        assert isinstance(debug_vcg, bool)
        assert isinstance(cvc5_binary, str) or cvc5_binary is None

        self.mh            = mh
        self.stab          = stab
        self.verify_checks = verify_checks
        self.debug_vcg     = debug_vcg
        self.cvc5_binary   = cvc5_binary

        self.abstract_extensions = {}
        self.checked_types       = set()

    def perform_sanity_checks(self):
        # lobster-exclude: Not safety relevant
        ok = True
        for package in self.stab.values(ast.Package):
            for n_typ in package.symbols.values(ast.Type):
                try:
                    self.verify_type(n_typ)
                except TRLC_Error:
                    ok = False

        # Complain about abstract types without extensions
        for package in self.stab.values(ast.Package):
            for n_typ in package.symbols.values(ast.Record_Type):
                if n_typ.is_abstract and not self.abstract_extensions[n_typ]:
                    self.mh.check(
                        n_typ.location,
                        "abstract type %s does not have any extensions" %
                        n_typ.name,
                        "abstract_leaf_types")

        return ok

    def verify_type(self, n_typ):
        # lobster-exclude: Not safety relevant
        assert isinstance(n_typ, ast.Type)

        if n_typ in self.checked_types:
            return
        else:
            self.checked_types.add(n_typ)

        if isinstance(n_typ, ast.Record_Type):
            self.verify_record_type(n_typ)

        elif isinstance(n_typ, ast.Tuple_Type):
            self.verify_tuple_type(n_typ)

        elif isinstance(n_typ, ast.Array_Type):
            self.verify_array_type(n_typ)

    def verify_tuple_type(self, n_tuple_type):
        assert isinstance(n_tuple_type, ast.Tuple_Type)

        # Detect confusing separators
        # lobster-trace: LRM.Tuple_Based_Literal_Ambiguity
        previous_was_int     = False
        previous_was_bad_sep = False
        bad_separator        = None
        location             = None
        for n_item in n_tuple_type.iter_sequence():
            if previous_was_bad_sep:
                assert isinstance(n_item, ast.Composite_Component)
                if isinstance(n_item.n_typ, ast.Builtin_Integer):
                    explanation = [
                        "For example 0%s100 would be a base %u literal" %
                        (bad_separator,
                         {"b" : 2, "x" : 16}[bad_separator]),
                        "instead of the tuple segment 0 %s 100." %
                        bad_separator
                    ]
                else:
                    explanation = [
                        "For example 0%s%s would be a lexer error" %
                        (bad_separator,
                         n_item.n_typ.get_example_value()),
                        "instead of the tuple segment 0 %s %s." %
                        (bad_separator,
                         n_item.n_typ.get_example_value())
                    ]

                self.mh.check(
                    location,
                    "%s separator after integer component"
                    " creates ambiguities" % bad_separator,
                    "separator_based_literal_ambiguity",
                    "\n".join(explanation))

            elif isinstance(n_item, ast.Composite_Component) and \
               isinstance(n_item.n_typ, ast.Builtin_Integer):
                previous_was_int = True

            elif isinstance(n_item, ast.Separator) and \
                 previous_was_int and \
                 n_item.to_string() in ("x", "b"):
                previous_was_bad_sep = True
                bad_separator        = n_item.to_string()
                location             = n_item.location

            else:
                previous_was_int     = False
                previous_was_bad_sep = False

        # Walk over components
        for n_component in n_tuple_type.components.values():
            self.verify_type(n_component.n_typ)

        # Verify checks
        if self.verify_checks:
            vcg = VCG(mh          = self.mh,
                      n_ctyp      = n_tuple_type,
                      debug       = self.debug_vcg,
                      use_api     = self.cvc5_binary is None,
                      cvc5_binary = self.cvc5_binary)
            vcg.analyze()

    def verify_record_type(self, n_record_type):
        # lobster-exclude: Not safety relevant
        assert isinstance(n_record_type, ast.Record_Type)

        # Mark abstract extensions
        if n_record_type.is_abstract:
            if n_record_type not in self.abstract_extensions:
                self.abstract_extensions[n_record_type] = set()
        elif n_record_type.parent and n_record_type.parent.is_abstract:
            if n_record_type.parent not in self.abstract_extensions:
                self.abstract_extensions[n_record_type.parent] = set()
            self.abstract_extensions[n_record_type.parent].add(n_record_type)

        # Walk over components
        for n_component in n_record_type.components.values():
            self.verify_type(n_component.n_typ)

        # Verify checks
        if self.verify_checks:
            vcg = VCG(mh          = self.mh,
                      n_ctyp      = n_record_type,
                      debug       = self.debug_vcg,
                      use_api     = self.cvc5_binary is None,
                      cvc5_binary = self.cvc5_binary)
            vcg.analyze()

    def verify_array_type(self, n_typ):
        # lobster-exclude: Not safety relevant
        assert isinstance(n_typ, ast.Array_Type)

        if n_typ.upper_bound is None:
            pass
        elif n_typ.lower_bound > n_typ.upper_bound:
            self.mh.check(n_typ.loc_upper,
                          "upper bound must be at least %u" %
                          n_typ.lower_bound,
                          "impossible_array_types")
        elif n_typ.upper_bound == 0:
            self.mh.check(n_typ.loc_upper,
                          "this array makes no sense",
                          "impossible_array_types")
        elif n_typ.upper_bound == 1 and n_typ.lower_bound == 1:
            self.mh.check(n_typ.loc_upper,
                          "array of fixed size 1 "
                          "should not be an array",
                          "weird_array_types",
                          "An array with a fixed size of 1 should not\n"
                          "be an array at all.")
        elif n_typ.upper_bound == 1 and n_typ.lower_bound == 0:
            self.mh.check(n_typ.loc_upper,
                          "consider making this array an"
                          " optional %s" % n_typ.element_type.name,
                          "weird_array_types",
                          "An array with 0 to 1 components should just\n"
                          "be an optional %s instead." %
                          n_typ.element_type.name)

    def markup_ref(self, item, string_literals):
        for string_literal in string_literals:
            for reference in string_literal.references:
                if reference.package.name == item.name:
                    return string_literal
        return None

    def verify_imports(self):
        for file in self.mh.sm.all_files.values():
            if not file.primary and not file.secondary:
                continue
            if not file.cu.imports:
                continue
            for item in file.cu.imports:
                import_tokens = [t for t in file.lexer.tokens
                                 if t.value == item.name]
                markup = self.markup_ref(item,
                                         (m.ast_link for m in
                                          file.lexer.tokens if
                                          isinstance(m.ast_link,
                                                     ast.String_Literal) and
                                          m.ast_link.has_references))
                if markup is not None:
                    import_tokens.append(markup)
                if len(import_tokens) == 1:
                    import_tk = import_tokens[0]
                    self.mh.check(import_tk.location,
                                    "unused import %s" % import_tk.value,
                                    "unused_imports",
                                    "Consider deleting this import"
                                    " statement if not needed.")
