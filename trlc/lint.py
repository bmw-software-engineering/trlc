#!/usr/bin/env python3
#
# TRLC - Treat Requirements Like Code
# Copyright (C) 2022 Bayerische Motoren Werke Aktiengesellschaft (BMW AG)
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

    def verify(self):
        ok = True
        for package in self.stab.values(ast.Package):
            for n_typ in package.symbols.values(ast.Record_Type):
                try:
                    self.verify_record(n_typ)
                except TRLC_Error:
                    ok = False

        # Complain about abstract types without extensions
        for package in self.stab.values(ast.Package):
            for n_typ in package.symbols.values(ast.Record_Type):
                if n_typ.is_abstract and not self.abstract_extensions[n_typ]:
                    self.mh.warning(
                        n_typ.location,
                        "abstract type %s does not have any extensions" %
                        n_typ.name)

        return ok

    def verify_record(self, n_record_type):
        assert isinstance(n_record_type, ast.Record_Type)

        # Mark abstract extensions
        if n_record_type.is_abstract:
            if n_record_type not in self.abstract_extensions:
                self.abstract_extensions[n_record_type] = set()
        elif n_record_type.parent and n_record_type.parent.is_abstract:
            if n_record_type.parent not in self.abstract_extensions:
                self.abstract_extensions[n_record_type.parent] = set()
            self.abstract_extensions[n_record_type.parent].add(n_record_type)
