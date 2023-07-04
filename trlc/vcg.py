#!/usr/bin/env python3
#
# TRLC - Treat Requirements Like Code
# Copyright (C) 2023 Bayerische Motoren Werke Aktiengesellschaft (BMW AG)
# Copyright (C) 2023 Florian Schanda
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

import subprocess

from trlc.ast import *
from trlc.errors import Location, Message_Handler

try:
    from pyvcg import smt
    from pyvcg import graph
    from pyvcg import vcg
    VCG_AVAILABLE = True
except ImportError:
    VCG_AVAILABLE = False


class Unsupported(Exception):
    def __init__(self, node, text):
        assert isinstance(node, Node)
        assert isinstance(text, str) or text is None
        super().__init__()
        self.message  = "%s not yet supported in VCG" % \
            (text if text else node.__class__.__name__)
        self.location = node.location


class VCG:
    def __init__(self, mh, n_ctyp):
        assert isinstance(mh, Message_Handler)
        assert isinstance(n_ctyp, Composite_Type)

        self.mh      = mh
        self.n_ctyp  = n_ctyp

        self.vc_name = "trlc-%s-%s" % (n_ctyp.n_package.name,
                                       n_ctyp.name)

        self.tmp_id = 0

        if VCG_AVAILABLE:
            self.vcg   = vcg.VCG()
            self.start = self.vcg.start
            self.graph = self.vcg.graph

        self.constants = {}

    @staticmethod
    def flag_unsupported(node, text=None):
        assert isinstance(node, Node)
        raise Unsupported(node, text)

    def new_temp_name(self):
        self.tmp_id += 1
        return "tmp.%u" % self.tmp_id

    def attach_validity_check(self, bool_expr):
        assert isinstance(bool_expr, smt.Expression)
        assert bool_expr.sort is smt.BUILTIN_BOOLEAN

        # Attach new graph node advance start
        gn_check = graph.Check(self.graph)
        gn_check.add_goal(bool_expr)
        self.start.add_edge_to(gn_check)
        self.start = gn_check

    def attach_assumption(self, bool_expr):
        assert isinstance(bool_expr, smt.Expression)
        assert bool_expr.sort is smt.BUILTIN_BOOLEAN

        # Attach new graph node advance start
        gn_ass = graph.Assumption(self.graph)
        gn_ass.add_statement(smt.Assertion(bool_expr))
        self.start.add_edge_to(gn_ass)
        self.start = gn_ass

    def attach_temp_declaration(self, node, sym, value=None):
        assert isinstance(node, Expression)
        assert isinstance(sym, smt.Constant)
        assert isinstance(value, smt.Expression) or value is None

        # Attach new graph node advance start
        gn_decl = graph.Assumption(self.graph)
        gn_decl.add_statement(
            smt.Constant_Declaration(
                symbol   = sym,
                value    = value,
                comment  = "result of %s at %s" % (node.to_string(),
                                                   node.location.to_string()),
                relevant = False))
        self.start.add_edge_to(gn_decl)
        self.start = gn_decl

    def analyze(self):
        if not VCG_AVAILABLE:
            return

        try:
            self.checks_on_composite_type(self.n_ctyp)
        except Unsupported as exc:
            self.mh.warning(exc.location,
                            exc.message)

    def checks_on_composite_type(self, n_ctyp):
        assert isinstance(n_ctyp, Composite_Type)

        # Create local variables
        gn_locals = graph.Assumption(self.graph)
        self.start.add_edge_to(gn_locals)
        self.start = gn_locals
        for n_component in n_ctyp.all_components():
            self.tr_component_decl(n_component, self.start)

        # Create paths for checks
        for n_check in n_ctyp.iter_checks():
            current_start = self.start
            self.tr_check(n_check)

            # Only fatal checks contribute to the total knowledge
            if n_check.severity != "fatal":
                self.start = current_start

        # Emit debug graph
        subprocess.run(["dot", "-Tpdf", "-o%s.pdf" % self.vc_name],
                       input = self.graph.debug_render_dot(),
                       check = True,
                       encoding = "UTF-8")

    def tr_component_value_name(self, n_component):
        return n_component.member_of.fully_qualified_name() + \
            "." + n_component.name + ".value"

    def tr_component_valid_name(self, n_component):
        return n_component.member_of.fully_qualified_name() + \
            "." + n_component.name + ".valid"

    def tr_component_decl(self, n_component, gn_locals):
        assert isinstance(n_component, Composite_Component)
        assert isinstance(gn_locals, graph.Assumption)

        id_value = self.tr_component_value_name(n_component)
        s_sort = self.tr_type(n_component.n_typ)
        s_sym  = smt.Constant(s_sort, id_value)
        # TODO: Frozen components
        s_val  = None
        s_decl = smt.Constant_Declaration(
            symbol   = s_sym,
            value    = s_val,
            comment  = "value for %s declared on %s" % (
                n_component.name,
                n_component.location.to_string()),
            relevant = True)
        gn_locals.add_statement(s_decl)
        self.constants[id_value] = s_sym

        id_valid = self.tr_component_valid_name(n_component)
        s_sym  = smt.Constant(smt.BUILTIN_BOOLEAN, id_valid)
        s_val  = (None
                  if n_component.optional
                  else smt.Boolean_Literal(True))
        s_decl = smt.Constant_Declaration(
            symbol   = s_sym,
            value    = s_val,
            relevant = True)
        gn_locals.add_statement(s_decl)
        self.constants[id_valid] = s_sym

    def tr_type(self, n_type):
        assert isinstance(n_type, Type)

        if isinstance(n_type, Builtin_Boolean):
            return smt.BUILTIN_BOOLEAN
        elif isinstance(n_type, Builtin_Integer):
            return smt.BUILTIN_INTEGER
        else:
            self.flag_unsupported(n_type)

    def tr_check(self, n_check):
        assert isinstance(n_check, Check)

        _, _ = self.tr_expression(n_check.n_expr)
        # TODO: Emit VC to test feasibility

    def tr_expression(self, n_expr):
        if isinstance(n_expr, Name_Reference):
            return self.tr_name_reference(n_expr)

        elif isinstance(n_expr, Binary_Expression):
            return self.tr_binary_expression(n_expr)

        elif isinstance(n_expr, Null_Literal):
            return None, smt.Boolean_Literal(False)

        else:
            self.flag_unsupported(n_expr)

    def tr_name_reference(self, n_ref):
        assert isinstance(n_ref, Name_Reference)

        if isinstance(n_ref.entity, Composite_Component):
            id_value = self.tr_component_value_name(n_ref.entity)
            id_valid = self.tr_component_valid_name(n_ref.entity)
            return self.constants[id_value], self.constants[id_valid]

        else:
            self.flag_unsupported(n_ref)

    def tr_binary_expression(self, n_expr):
        assert isinstance(n_expr, Binary_Expression)

        if n_expr.operator in (Binary_Operator.COMP_EQ,
                               Binary_Operator.COMP_NEQ):
            return self.tr_op_equality(n_expr)

        if n_expr.operator == Binary_Operator.LOGICAL_IMPLIES:
            lhs_value, lhs_valid = self.tr_expression(n_expr.n_lhs)
            # Emit VC for validity
            self.attach_validity_check(lhs_valid)

            # Split into two paths.
            current_start = self.start
            sym_result = smt.Constant(smt.BUILTIN_BOOLEAN,
                                      self.new_temp_name())
            gn_end = graph.Node(self.graph)

            ### 1: Implication is not valid
            self.start = current_start
            self.attach_assumption(smt.Boolean_Negation(lhs_value))
            self.attach_temp_declaration(n_expr,
                                         sym_result,
                                         smt.Boolean_Literal(True))
            self.start.add_edge_to(gn_end)

            ### 2: Implication is valid.
            self.start = current_start
            self.attach_assumption(lhs_value)
            rhs_value, rhs_valid = self.tr_expression(n_expr.n_rhs)
            self.attach_validity_check(rhs_valid)
            self.attach_temp_declaration(n_expr,
                                         sym_result,
                                         rhs_value)
            self.start.add_edge_to(gn_end)

            # Join paths
            self.start = gn_end

            return sym_result, smt.Boolean_Literal(True)

        else:
            self.flag_unsupported(n_expr, n_expr.operator.name)

    def tr_op_equality(self, n_expr):
        assert isinstance(n_expr, Binary_Expression)
        assert n_expr.operator in (Binary_Operator.COMP_EQ,
                                   Binary_Operator.COMP_NEQ)

        lhs_value, lhs_valid = self.tr_expression(n_expr.n_lhs)
        rhs_value, rhs_valid = self.tr_expression(n_expr.n_rhs)

        if lhs_valid.is_static_true() and rhs_valid.is_static_true():
            # Simplified form, this is just x == y
            result = smt.Comparison("=", lhs_value, rhs_value)

        elif lhs_valid.is_static_false() and rhs_valid.is_static_false():
            # This is null == null, so true
            result = smt.Boolean_Literal(True)

        elif lhs_value is None:
            # This is null == <expr>, true iff rhs is null
            result = smt.Boolean_Negation(rhs_valid)

        elif rhs_value is None:
            # This is <expr> == null, true iff lhs is null
            result = smt.Boolean_Negation(lhs_valid)

        else:
            # This is <expr> == <expr> without shortcuts
            result = smt.Conjunction(
                smt.Comparison("=", lhs_valid, rhs_valid),
                smt.Implication(lhs_valid,
                                smt.Comparison("=", lhs_value, rhs_value)))

        if n_expr.operator == Binary_Operator.COMP_NEQ:
            result = smt.Boolean_Negation(result)

        sym_result = smt.Constant(smt.BUILTIN_BOOLEAN,
                                  self.new_temp_name())
        self.attach_temp_declaration(n_expr, sym_result, result)

        return sym_result, smt.Boolean_Literal(True)
