#!/usr/bin/env python3
#
# TRLC - Treat Requirements Like Code
# Copyright (C) 2023 Bayerische Motoren Werke Aktiengesellschaft (BMW AG)
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

import os

from trlc.ast import *
from trlc.errors import Message_Handler

PREAMBLE = """
"""


class VCG:
    def __init__(self, mh, n_ctyp):
        assert isinstance(mh, Message_Handler)
        assert isinstance(n_ctyp, Composite_Type)

        self.mh     = mh
        self.n_ctyp = n_ctyp

        self.vc_name = "trlc-%s-%s" % (n_ctyp.n_package.name,
                                       n_ctyp.name)
        self.vc_id   = 0

        self.types  = {}
        self.tmp_id = 0

        self.logics = []
        self.decl   = []
        self.hyp    = []

        self.push_stack()

    def get_tmp_id(self):
        self.tmp_id += 1
        return ("tmp_%u"   % self.tmp_id,
                "valid_%u" % self.tmp_id)

    def push_stack(self):
        self.logics.append(set())
        self.decl.append([])
        self.hyp.append([])

    def pop_stack(self):
        assert len(self.decl) > 1

        self.logics.pop()
        self.decl.pop()
        self.hyp.pop()

    def add_logic(self, logic):
        assert logic in ("int", "int_nl", "real", "real_nl", "bv",
                         "quant", "dt", "uf", "arrays", "strings", "regex")
        self.logics[-1].add(logic)

    def add_decl(self, decl):
        self.decl[-1].append(decl)

    def add_hyp(self, hyp):
        self.hyp[-1].append(hyp)

    def gen_decl(self, name, optional, typ):
        assert isinstance(name, str)
        assert isinstance(optional, bool)
        assert isinstance(typ, Type)

    def gen_logic(self):
        return "ALL"  # FIXME

    def emit_vc(self, goal):
        self.vc_id += 1

        vc = []
        vc.append("(set-logic %s)" % self.gen_logic())
        vc.append("(set-option :produce-models true)")
        vc += PREAMBLE.splitlines()
        vc.append("")
        vc.append(";; declarations")
        for items in self.decl:
            vc += items
        vc.append("")
        vc.append(";; assumptions")
        for items in self.hyp:
            vc += items
        vc.append("")
        vc.append(";; goal")
        vc.append("(assert (not %s))" % goal)
        vc.append("")
        vc.append("(check-sat)")
        vc.append("(exit)")
        print("\n".join(vc))
        filename = "%s-%u.smt2" % (self.vc_name, self.vc_id)
        with open(filename, "w", encoding="UTF-8") as fd:
            fd.write("\n".join(vc))
            fd.write("\n")
        os.system("cvc5 %s" % filename)

    def analyze(self):
        pass

    def tr_expression(self, n_expr):
        assert isinstance(n_expr, Expression)

        if isinstance(n_expr, Binary_Expression):
            return self.tr_bin_expression(n_expr)

        else:
            self.mh.ice_loc(n_expr.location,
                            "unexpected expression class %s" %
                            n_expr.__class__.__name__)

    def tr_bin_expression(self, n_expr):
        assert isinstance(n_expr, Binary_Expression)
