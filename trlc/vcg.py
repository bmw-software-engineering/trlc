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


class Feedback:
    def __init__(self, node, message, expect_unsat=True):
        assert isinstance(node, Expression)
        assert isinstance(message, str)
        assert isinstance(expect_unsat, bool)
        self.node         = node
        self.message      = message
        self.expect_unsat = expect_unsat


class VCG:
    def __init__(self, mh, n_ctyp, debug):
        assert VCG_AVAILABLE
        assert isinstance(mh, Message_Handler)
        assert isinstance(n_ctyp, Composite_Type)
        assert isinstance(debug, bool)

        self.mh      = mh
        self.n_ctyp  = n_ctyp
        self.debug   = debug

        self.vc_name = "trlc-%s-%s" % (n_ctyp.n_package.name,
                                       n_ctyp.name)

        self.tmp_id = 0

        self.vcg   = vcg.VCG()
        self.start = self.vcg.start
        self.graph = self.vcg.graph

        self.constants    = {}
        self.enumerations = {}
        self.arrays       = {}

    @staticmethod
    def flag_unsupported(node, text=None):
        assert isinstance(node, Node)
        raise Unsupported(node, text)

    def new_temp_name(self):
        self.tmp_id += 1
        return "tmp.%u" % self.tmp_id

    def attach_validity_check(self, bool_expr, origin):
        assert isinstance(bool_expr, smt.Expression)
        assert bool_expr.sort is smt.BUILTIN_BOOLEAN
        assert isinstance(origin, Expression)

        # Attach new graph node advance start
        if not bool_expr.is_static_true():
            gn_check = graph.Check(self.graph)
            gn_check.add_goal(bool_expr,
                              Feedback(origin,
                                       "expression could be null"),
                              "validity check for %s" % origin.to_string())
            self.start.add_edge_to(gn_check)
            self.start = gn_check

    def attach_int_division_check(self, int_expr, origin):
        assert isinstance(int_expr, smt.Expression)
        assert int_expr.sort is smt.BUILTIN_INTEGER
        assert isinstance(origin, Expression)

        # Attach new graph node advance start
        gn_check = graph.Check(self.graph)
        gn_check.add_goal(
            smt.Boolean_Negation(
                smt.Comparison("=", int_expr, smt.Integer_Literal(0))),
            Feedback(origin,
                     "divisor could be 0"),
            "division by zero check for %s" % origin.to_string())
        self.start.add_edge_to(gn_check)
        self.start = gn_check

    def attach_index_check(self, seq_expr, index_expr, origin):
        assert isinstance(seq_expr, smt.Expression)
        assert isinstance(seq_expr.sort, smt.Sequence_Sort)
        assert isinstance(index_expr, smt.Expression)
        assert index_expr.sort is smt.BUILTIN_INTEGER
        assert isinstance(origin, Binary_Expression)
        assert origin.operator == Binary_Operator.INDEX

        # Attach new graph node advance start
        gn_check = graph.Check(self.graph)
        gn_check.add_goal(
            smt.Comparison(">=", index_expr, smt.Integer_Literal(0)),
            Feedback(origin,
                     "array index could be less than 0"),
            "index lower bound check for %s" % origin.to_string())
        gn_check.add_goal(
            smt.Comparison("<",
                           index_expr,
                           smt.Sequence_Length(seq_expr)),
            Feedback(origin,
                     "array index could be larger than len(%s)" %
                     origin.n_lhs.to_string()),
            "index lower bound check for %s" % origin.to_string())

        self.start.add_edge_to(gn_check)
        self.start = gn_check

    def attach_feasability_check(self, bool_expr, origin):
        assert isinstance(bool_expr, smt.Expression)
        assert bool_expr.sort is smt.BUILTIN_BOOLEAN
        assert isinstance(origin, Expression)

        # Attach new graph node advance start
        gn_check = graph.Check(self.graph)
        gn_check.add_goal(bool_expr,
                          Feedback(origin,
                                   "expression is always true",
                                   expect_unsat = False),
                          "feasability check for %s" % origin.to_string())
        self.start.add_edge_to(gn_check)

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
        try:
            self.checks_on_composite_type(self.n_ctyp)
        except Unsupported as exc:
            self.mh.warning(exc.location,
                            exc.message)
            return

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
        if self.debug:
            subprocess.run(["dot", "-Tpdf", "-o%s.pdf" % self.vc_name],
                           input = self.graph.debug_render_dot(),
                           check = True,
                           encoding = "UTF-8")

        # Generate VCs
        self.vcg.generate()

        # Solve VCs and provide feedback
        nok_feasibility_checks = []
        ok_feasibility_checks  = set()
        nok_validity_checks    = set()

        for vc_id, vc in enumerate(self.vcg.vcs):
            if self.debug:
                with open(self.vc_name + "_%04u.smt2" % vc_id, "w",
                          encoding="UTF-8") as fd:
                    fd.write(vc["script"].generate_vc(smt.SMTLIB_Generator()))

            # Checks that have already failed don't need to be checked
            # again on a different path
            if vc["feedback"].expect_unsat and \
               vc["feedback"] in nok_validity_checks:
                continue

            status, values = vc["script"].solve_vc(smt.CVC5_Solver())

            if vc["feedback"].expect_unsat:
                if status != "unsat":
                    self.mh.failed_vc(vc["feedback"].node.location,
                                      vc["feedback"].message,
                                      self.create_counterexample(values))
                    nok_validity_checks.add(vc["feedback"])
            else:
                if status == "unsat":
                    nok_feasibility_checks.append(vc["feedback"])
                else:
                    ok_feasibility_checks.add(vc["feedback"])

        # This is a bit wonky, but this way we make sure the ording is
        # consistent
        for feedback in nok_feasibility_checks:
            if feedback not in ok_feasibility_checks:
                self.mh.failed_vc(feedback.node.location,
                                  feedback.message)
                ok_feasibility_checks.add(feedback)

    def create_counterexample(self, values):
        rv = [
            "example %s triggering error:" %
            self.n_ctyp.__class__.__name__.lower(),
            "  %s bad_potato {" % self.n_ctyp.name
        ]

        for n_component in self.n_ctyp.all_components():
            id_value = self.tr_component_value_name(n_component)
            id_valid = self.tr_component_valid_name(n_component)
            if values[id_valid]:
                rv.append("    %s = %s" %
                          (n_component.name,
                           self.value_to_trlc(n_component.n_typ,
                                              values[id_value])))
            else:
                rv.append("    /* %s is null */" % n_component.name)

        rv.append("  }")
        return "\n".join(rv)

    def value_to_trlc(self, n_typ, value):
        assert isinstance(n_typ, Type)

        if isinstance(n_typ, Builtin_Integer):
            return str(value)

        elif isinstance(n_typ, Builtin_Boolean):
            return "true" if value else "false"

        elif isinstance(n_typ, Enumeration_Type):
            return n_typ.name + "." + value

        elif isinstance(n_typ, Builtin_String):
            if "\n" in value:
                return "'''%s'''" % value
            else:
                return '"%s"' % value

        elif isinstance(n_typ, Record_Type):
            if n_typ.n_package is self.n_ctyp.n_package:
                return "%s_instance_%i" % (n_typ.name, value)
            else:
                return "%s.%s_instance_%i" % (n_typ.n_package.name,
                                              n_typ.name,
                                              value)

        elif isinstance(n_typ, Array_Type):
            return "[%s]" % ", ".join(self.value_to_trlc(n_typ.element_type,
                                                         item)
                                      for item in value)

        else:
            self.flag_unsupported(n_typ,
                                  "back-conversion from %s" % n_typ.name)

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

        # For arrays we need to add additional constraints for the
        # length
        if isinstance(n_component.n_typ, Array_Type):
            if n_component.n_typ.lower_bound > 0:
                s_lower = smt.Integer_Literal(n_component.n_typ.lower_bound)
                gn_locals.add_statement(
                    smt.Assertion(
                        smt.Comparison(">=",
                                       smt.Sequence_Length(s_sym),
                                       s_lower)))

            if n_component.n_typ.upper_bound is not None:
                s_upper = smt.Integer_Literal(n_component.n_typ.upper_bound)
                gn_locals.add_statement(
                    smt.Assertion(
                        smt.Comparison("<=",
                                       smt.Sequence_Length(s_sym),
                                       s_upper)))

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

        elif isinstance(n_type, Builtin_String):
            return smt.BUILTIN_STRING

        elif isinstance(n_type, Enumeration_Type):
            if n_type not in self.enumerations:
                s_sort = smt.Enumeration(n_type.n_package.name +
                                         "." + n_type.name)
                for n_lit in n_type.literals.values():
                    s_sort.add_literal(n_lit.name)
                self.enumerations[n_type] = s_sort
                self.start.add_statement(
                    smt.Enumeration_Declaration(
                        s_sort,
                        "enumeration %s from %s" % (
                            n_type.name,
                            n_type.location.to_string())))
            return self.enumerations[n_type]

        elif isinstance(n_type, Array_Type):
            if n_type not in self.arrays:
                s_element_sort = self.tr_type(n_type.element_type)
                s_sequence = smt.Sequence_Sort(s_element_sort)
                self.arrays[n_type] = s_sequence

            return self.arrays[n_type]

        elif isinstance(n_type, Record_Type):
            # Record references are modelled as a free integer, since
            # we can't really _do_ anything with them. We just need a
            # variable with infinite range so we can generate
            # arbitrary fictional record names
            return smt.BUILTIN_INTEGER

        else:
            self.flag_unsupported(n_type)

    def tr_check(self, n_check):
        assert isinstance(n_check, Check)

        value, valid = self.tr_expression(n_check.n_expr)
        self.attach_validity_check(valid, n_check.n_expr)
        self.attach_feasability_check(value, n_check.n_expr)
        self.attach_assumption(value)

    def tr_expression(self, n_expr):
        value = None

        if isinstance(n_expr, Name_Reference):
            return self.tr_name_reference(n_expr)

        elif isinstance(n_expr, Unary_Expression):
            return self.tr_unary_expression(n_expr)

        elif isinstance(n_expr, Binary_Expression):
            return self.tr_binary_expression(n_expr)

        elif isinstance(n_expr, Null_Literal):
            return None, smt.Boolean_Literal(False)

        elif isinstance(n_expr, Boolean_Literal):
            value = smt.Boolean_Literal(n_expr.value)

        elif isinstance(n_expr, Integer_Literal):
            value = smt.Integer_Literal(n_expr.value)

        elif isinstance(n_expr, Enumeration_Literal):
            value = smt.Enumeration_Literal(self.tr_type(n_expr.typ),
                                            n_expr.value.name)

        elif isinstance(n_expr, String_Literal):
            value = smt.String_Literal(n_expr.value)

        else:
            self.flag_unsupported(n_expr)

        return value, smt.Boolean_Literal(True)

    def tr_name_reference(self, n_ref):
        assert isinstance(n_ref, Name_Reference)

        if isinstance(n_ref.entity, Composite_Component):
            id_value = self.tr_component_value_name(n_ref.entity)
            id_valid = self.tr_component_valid_name(n_ref.entity)
            return self.constants[id_value], self.constants[id_valid]

        else:
            self.flag_unsupported(n_ref)

    def tr_unary_expression(self, n_expr):
        assert isinstance(n_expr, Unary_Expression)

        operand_value, operand_valid = self.tr_expression(n_expr.n_operand)
        self.attach_validity_check(operand_valid, n_expr.n_operand)

        sym_result = smt.Constant(self.tr_type(n_expr.typ),
                                  self.new_temp_name())
        sym_value = None

        if n_expr.operator == Unary_Operator.MINUS:
            if isinstance(n_expr.n_operand.typ, Builtin_Integer):
                sym_value = smt.Unary_Int_Arithmetic_Op("-",
                                                        operand_value)

            else:
                self.flag_unsupported(n_expr,
                                      n_expr.operator.name +
                                      " for non-integer")

        elif n_expr.operator == Unary_Operator.PLUS:
            sym_value = operand_value

        elif n_expr.operator == Unary_Operator.LOGICAL_NOT:
            sym_value = smt.Boolean_Negation(operand_value)

        elif n_expr.operator == Unary_Operator.ABSOLUTE_VALUE:
            if isinstance(n_expr.n_operand.typ, Builtin_Integer):
                sym_value = smt.Unary_Int_Arithmetic_Op("abs",
                                                        operand_value)

            else:
                self.flag_unsupported(n_expr,
                                      n_expr.operator.name +
                                      " for non-integer")

        elif n_expr.operator == Unary_Operator.STRING_LENGTH:
            sym_value = smt.String_Length(operand_value)

        elif n_expr.operator == Unary_Operator.ARRAY_LENGTH:
            sym_value = smt.Sequence_Length(operand_value)

        else:
            self.flag_unsupported(n_expr,
                                  n_expr.operator.name)

        self.attach_temp_declaration(n_expr,
                                     sym_result,
                                     sym_value)
        return sym_result, smt.Boolean_Literal(True)

    def tr_binary_expression(self, n_expr):
        assert isinstance(n_expr, Binary_Expression)

        # Some operators deal with validity in a different way. We
        # deal with them first and then exit.
        if n_expr.operator in (Binary_Operator.COMP_EQ,
                               Binary_Operator.COMP_NEQ):
            return self.tr_op_equality(n_expr)

        elif n_expr.operator == Binary_Operator.LOGICAL_IMPLIES:
            return self.tr_op_implication(n_expr)

        elif n_expr.operator == Binary_Operator.LOGICAL_AND:
            return self.tr_op_and(n_expr)

        # The remaining operators always check for validity, so we can
        # obtain the values of both sides now.
        lhs_value, lhs_valid = self.tr_expression(n_expr.n_lhs)
        self.attach_validity_check(lhs_valid, n_expr.n_lhs)
        rhs_value, rhs_valid = self.tr_expression(n_expr.n_rhs)
        self.attach_validity_check(rhs_valid, n_expr.n_rhs)
        sym_result = smt.Constant(self.tr_type(n_expr.typ),
                                  self.new_temp_name())
        sym_value = None

        if n_expr.operator in (Binary_Operator.PLUS,
                               Binary_Operator.MINUS,
                               Binary_Operator.TIMES,
                               Binary_Operator.DIVIDE,
                               Binary_Operator.REMAINDER):

            smt_op = {
                Binary_Operator.PLUS      : "+",
                Binary_Operator.MINUS     : "-",
                Binary_Operator.TIMES     : "*",
                Binary_Operator.DIVIDE    : "floor_div",
                Binary_Operator.REMAINDER : "ada_remainder",
            }[n_expr.operator]

            if isinstance(n_expr.n_lhs.typ, Builtin_Integer):
                if n_expr.operator in (Binary_Operator.DIVIDE,
                                       Binary_Operator.REMAINDER):
                    self.attach_int_division_check(rhs_value, n_expr)

                sym_value = smt.Binary_Int_Arithmetic_Op(smt_op,
                                                         lhs_value,
                                                         rhs_value)

            else:
                self.flag_unsupported(n_expr,
                                      n_expr.operator.name +
                                      " for non-integer")

        elif n_expr.operator in (Binary_Operator.COMP_LT,
                                 Binary_Operator.COMP_LEQ,
                                 Binary_Operator.COMP_GT,
                                 Binary_Operator.COMP_GEQ):
            smt_op = {
                Binary_Operator.COMP_LT  : "<",
                Binary_Operator.COMP_LEQ : "<=",
                Binary_Operator.COMP_GT  : ">",
                Binary_Operator.COMP_GEQ : ">=",
            }[n_expr.operator]

            sym_value = smt.Comparison(smt_op, lhs_value, rhs_value)

        elif n_expr.operator in (Binary_Operator.STRING_CONTAINS,
                                 Binary_Operator.STRING_STARTSWITH,
                                 Binary_Operator.STRING_ENDSWITH):

            smt_op = {
                Binary_Operator.STRING_CONTAINS   : "contains",
                Binary_Operator.STRING_STARTSWITH : "prefixof",
                Binary_Operator.STRING_ENDSWITH   : "suffixof"
            }

            # LHS / RHS ordering is not a mistake, in SMTLIB it's the
            # other way around than in TRLC.
            sym_value = smt.String_Predicate(smt_op[n_expr.operator],
                                             rhs_value,
                                             lhs_value)

        elif n_expr.operator == Binary_Operator.INDEX:
            self.attach_index_check(lhs_value, rhs_value, n_expr)
            sym_value = smt.Sequence_Index(lhs_value, rhs_value)

        elif n_expr.operator == Binary_Operator.ARRAY_CONTAINS:
            sym_value = smt.Sequence_Contains(rhs_value, lhs_value)

        else:
            self.flag_unsupported(n_expr, n_expr.operator.name)

        self.attach_temp_declaration(n_expr,
                                     sym_result,
                                     sym_value)
        return sym_result, smt.Boolean_Literal(True)

    def tr_op_implication(self, n_expr):
        assert isinstance(n_expr, Binary_Expression)
        assert n_expr.operator == Binary_Operator.LOGICAL_IMPLIES

        lhs_value, lhs_valid = self.tr_expression(n_expr.n_lhs)
        # Emit VC for validity
        self.attach_validity_check(lhs_valid, n_expr.n_lhs)

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
        self.attach_validity_check(rhs_valid, n_expr.n_rhs)
        self.attach_temp_declaration(n_expr,
                                     sym_result,
                                     rhs_value)
        self.start.add_edge_to(gn_end)

        # Join paths
        self.start = gn_end

        return sym_result, smt.Boolean_Literal(True)

    def tr_op_and(self, n_expr):
        assert isinstance(n_expr, Binary_Expression)
        assert n_expr.operator == Binary_Operator.LOGICAL_AND

        lhs_value, lhs_valid = self.tr_expression(n_expr.n_lhs)
        # Emit VC for validity
        self.attach_validity_check(lhs_valid, n_expr.n_lhs)

        # Split into two paths.
        current_start = self.start
        sym_result = smt.Constant(smt.BUILTIN_BOOLEAN,
                                  self.new_temp_name())
        gn_end = graph.Node(self.graph)

        ### 1: LHS is not true
        self.start = current_start
        self.attach_assumption(smt.Boolean_Negation(lhs_value))
        self.attach_temp_declaration(n_expr,
                                     sym_result,
                                     smt.Boolean_Literal(False))
        self.start.add_edge_to(gn_end)

        ### 2: LHS is true
        self.start = current_start
        self.attach_assumption(lhs_value)
        rhs_value, rhs_valid = self.tr_expression(n_expr.n_rhs)
        self.attach_validity_check(rhs_valid, n_expr.n_rhs)
        self.attach_temp_declaration(n_expr,
                                     sym_result,
                                     rhs_value)
        self.start.add_edge_to(gn_end)

        # Join paths
        self.start = gn_end

        return sym_result, smt.Boolean_Literal(True)

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
