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


class Linter:
    def __init__(self, mh, stab):
        assert isinstance(mh, Message_Handler)
        assert isinstance(stab, ast.Symbol_Table)

        self.mh   = mh
        self.stab = stab

        self.abstract_extensions = {}
        self.checked_types = set()

    def verify(self):
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
        previous_was_int = False
        for n_item in n_tuple_type.iter_sequence():
            if isinstance(n_item, ast.Composite_Component) and \
               isinstance(n_item.n_typ, ast.Builtin_Integer):
                previous_was_int = True
            elif isinstance(n_item, ast.Separator) and previous_was_int:
                if n_item.token.kind == "IDENTIFIER" and \
                   n_item.token.value in ("x", "b"):
                    self.mh.check(n_item.location,
                                  "%s separator after integer component"
                                  " creates ambiguities with base %u literals"
                                  % (n_item.token.value,
                                     2 if n_item.token.value == "b" else 16),
                                  "separator_based_literal_ambiguity")
            else:
                previous_was_int = False

        # Walk over components
        for n_component in n_tuple_type.components.values():
            self.verify_type(n_component.n_typ)

    def verify_record_type(self, n_record_type):
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

    def verify_array_type(self, n_typ):
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
                          "weird_array_types")
        elif n_typ.upper_bound == 1 and n_typ.lower_bound == 0:
            self.mh.check(n_typ.loc_upper,
                          "consider making this array an"
                          " optional %s" % n_typ.element_type.name,
                          "weird_array_types")
