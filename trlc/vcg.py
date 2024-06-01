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
    from pyvcg.driver.file_smtlib import SMTLIB_Generator
    from pyvcg.driver.cvc5_smtlib import CVC5_File_Solver
    VCG_AVAILABLE = True
except ImportError:  # pragma: no cover
    VCG_AVAILABLE = False

try:
    from pyvcg.driver.cvc5_api import CVC5_Solver
    CVC5_API_AVAILABLE = True
except ImportError:  # pragma: no cover
    CVC5_API_AVAILABLE = False

CVC5_OPTIONS = {
    "tlimit-per"      : 2500,
    "seed"            : 42,
    "sat-random-seed" : 42,
}


class Unsupported(Exception):  # pragma: no cover
    # lobster-exclude: Not safety relevant
    def __init__(self, node, text):
        assert isinstance(node, Node)
        assert isinstance(text, str) or text is None
        super().__init__()
        self.message  = "%s not yet supported in VCG" % \
            (text if text else node.__class__.__name__)
        self.location = node.location


class Feedback:
    # lobster-exclude: Not safety relevant
    def __init__(self, node, message, kind, expect_unsat=True):
        assert isinstance(node, Expression)
        assert isinstance(message, str)
        assert isinstance(kind, str)
        assert isinstance(expect_unsat, bool)
        self.node         = node
        self.message      = message
        self.kind         = "vcg-" + kind
        self.expect_unsat = expect_unsat


class VCG:
    # lobster-exclude: Not safety relevant
    def __init__(self, mh, n_ctyp, debug, use_api=True, cvc5_binary=None):
        assert VCG_AVAILABLE
        assert isinstance(mh, Message_Handler)
        assert isinstance(n_ctyp, Composite_Type)
        assert isinstance(debug, bool)
        assert isinstance(use_api, bool)
        assert use_api or isinstance(cvc5_binary, str)

        self.mh       = mh
        self.n_ctyp   = n_ctyp
        self.debug    = debug
        self.use_api  = use_api
        self.cvc5_bin = cvc5_binary

        self.vc_name = "trlc-%s-%s" % (n_ctyp.n_package.name,
                                       n_ctyp.name)

        self.tmp_id = 0

        self.vcg      = vcg.VCG()
        self.graph    = self.vcg.graph
        self.start    = self.vcg.start
        # Current start node, we will update this as we go along.
        self.preamble = None
        # We do remember the first node where we put all our
        # declarations, in case we need to add some more later.

        self.constants    = {}
        self.enumerations = {}
        self.tuples       = {}
        self.arrays       = {}
        self.bound_vars   = {}
        self.qe_vars      = {}
        self.tuple_base   = {}

        self.uf_matches   = None
        # Pointer to the UF we use for matches. We only generate it
        # when we must, as it may affect the logics selected due to
        # string theory being used.

        self.functional   = False
        # If set to true, then we ignore validity checks and do not
        # create intermediates. We just build the value and validity
        # expresions and return them.

        self.emit_checks  = True
        # If set to false, we skip creating checks.

    @staticmethod
    def flag_unsupported(node, text=None):  # pragma: no cover
        assert isinstance(node, Node)
        raise Unsupported(node, text)

    def new_temp_name(self):
        self.tmp_id += 1
        return "tmp.%u" % self.tmp_id

    def get_uf_matches(self):
        if self.uf_matches is None:
            self.uf_matches = \
                smt.Function("trlc.matches",
                             smt.BUILTIN_BOOLEAN,
                             smt.Bound_Variable(smt.BUILTIN_STRING,
                                                "subject"),
                             smt.Bound_Variable(smt.BUILTIN_STRING,
                                                "regex"))

            # Create UF for the matches function (for now, later we
            # will deal with regex properly).
            self.preamble.add_statement(
                smt.Function_Declaration(self.uf_matches))

        return self.uf_matches

    def create_return(self, node, s_value, s_valid=None):
        assert isinstance(node, Expression)
        assert isinstance(s_value, smt.Expression)
        assert isinstance(s_valid, smt.Expression) or s_valid is None

        if s_valid is None:
            s_valid = smt.Boolean_Literal(True)

        if self.functional:
            return s_value, s_valid

        else:
            sym_result = smt.Constant(s_value.sort,
                                      self.new_temp_name())
            self.attach_temp_declaration(node, sym_result, s_value)

            return sym_result, s_valid

    def attach_validity_check(self, bool_expr, origin):
        assert isinstance(bool_expr, smt.Expression)
        assert bool_expr.sort is smt.BUILTIN_BOOLEAN
        assert isinstance(origin, Expression)
        assert not self.functional

        if not self.emit_checks:
            return

        # Attach new graph node advance start
        if not bool_expr.is_static_true():
            gn_check = graph.Check(self.graph)
            gn_check.add_goal(bool_expr,
                              Feedback(origin,
                                       "expression could be null",
                                       "evaluation-of-null"),
                              "validity check for %s" % origin.to_string())
            self.start.add_edge_to(gn_check)
            self.start = gn_check

    def attach_int_division_check(self, int_expr, origin):
        assert isinstance(int_expr, smt.Expression)
        assert int_expr.sort is smt.BUILTIN_INTEGER
        assert isinstance(origin, Expression)
        assert not self.functional

        if not self.emit_checks:
            return

        # Attach new graph node advance start
        gn_check = graph.Check(self.graph)
        gn_check.add_goal(
            smt.Boolean_Negation(
                smt.Comparison("=", int_expr, smt.Integer_Literal(0))),
            Feedback(origin,
                     "divisor could be 0",
                     "div-by-zero"),
            "division by zero check for %s" % origin.to_string())
        self.start.add_edge_to(gn_check)
        self.start = gn_check

    def attach_real_division_check(self, real_expr, origin):
        assert isinstance(real_expr, smt.Expression)
        assert real_expr.sort is smt.BUILTIN_REAL
        assert isinstance(origin, Expression)
        assert not self.functional

        if not self.emit_checks:
            return

        # Attach new graph node advance start
        gn_check = graph.Check(self.graph)
        gn_check.add_goal(
            smt.Boolean_Negation(
                smt.Comparison("=", real_expr, smt.Real_Literal(0))),
            Feedback(origin,
                     "divisor could be 0.0",
                     "div-by-zero"),
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
        assert not self.functional

        if not self.emit_checks:
            return

        # Attach new graph node advance start
        gn_check = graph.Check(self.graph)
        gn_check.add_goal(
            smt.Comparison(">=", index_expr, smt.Integer_Literal(0)),
            Feedback(origin,
                     "array index could be less than 0",
                     "array-index"),
            "index lower bound check for %s" % origin.to_string())
        gn_check.add_goal(
            smt.Comparison("<",
                           index_expr,
                           smt.Sequence_Length(seq_expr)),
            Feedback(origin,
                     "array index could be larger than len(%s)" %
                     origin.n_lhs.to_string(),
                     "array-index"),
            "index lower bound check for %s" % origin.to_string())

        self.start.add_edge_to(gn_check)
        self.start = gn_check

    def attach_feasability_check(self, bool_expr, origin):
        assert isinstance(bool_expr, smt.Expression)
        assert bool_expr.sort is smt.BUILTIN_BOOLEAN
        assert isinstance(origin, Expression)
        assert not self.functional

        if not self.emit_checks:
            return

        # Attach new graph node advance start
        gn_check = graph.Check(self.graph)
        gn_check.add_goal(bool_expr,
                          Feedback(origin,
                                   "expression is always true",
                                   "always-true",
                                   expect_unsat = False),
                          "feasability check for %s" % origin.to_string())
        self.start.add_edge_to(gn_check)

    def attach_assumption(self, bool_expr):
        assert isinstance(bool_expr, smt.Expression)
        assert bool_expr.sort is smt.BUILTIN_BOOLEAN
        assert not self.functional

        # Attach new graph node advance start
        gn_ass = graph.Assumption(self.graph)
        gn_ass.add_statement(smt.Assertion(bool_expr))
        self.start.add_edge_to(gn_ass)
        self.start = gn_ass

    def attach_temp_declaration(self, node, sym, value=None):
        assert isinstance(node, (Expression, Action))
        assert isinstance(sym, smt.Constant)
        assert isinstance(value, smt.Expression) or value is None
        assert not self.functional

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

    def attach_empty_assumption(self):
        assert not self.functional

        # Attach new graph node advance start
        gn_decl = graph.Assumption(self.graph)
        self.start.add_edge_to(gn_decl)
        self.start = gn_decl

    def analyze(self):
        try:
            self.checks_on_composite_type(self.n_ctyp)
        except Unsupported as exc:  # pragma: no cover
            self.mh.warning(exc.location,
                            exc.message)

    def checks_on_composite_type(self, n_ctyp):
        assert isinstance(n_ctyp, Composite_Type)

        # Create node for global declarations
        gn_locals = graph.Assumption(self.graph)
        self.start.add_edge_to(gn_locals)
        self.start    = gn_locals
        self.preamble = gn_locals

        # Create local variables
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
        if self.debug:  # pragma: no cover
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
            if self.debug:  # pramga: no cover
                with open(self.vc_name + "_%04u.smt2" % vc_id, "w",
                          encoding="UTF-8") as fd:
                    fd.write(vc["script"].generate_vc(SMTLIB_Generator()))

            # Checks that have already failed don't need to be checked
            # again on a different path
            if vc["feedback"].expect_unsat and \
               vc["feedback"] in nok_validity_checks:
                continue

            if self.use_api:
                solver = CVC5_Solver()
            else:
                solver = CVC5_File_Solver(self.cvc5_bin)
            for name, value in CVC5_OPTIONS.items():
                solver.set_solver_option(name, value)

            status, values = vc["script"].solve_vc(solver)

            message = vc["feedback"].message
            if self.debug:  # pragma: no cover
                message += " [vc_id = %u]" % vc_id

            if vc["feedback"].expect_unsat:
                if status != "unsat":
                    self.mh.check(vc["feedback"].node.location,
                                  message,
                                  vc["feedback"].kind,
                                  self.create_counterexample(status,
                                                             values))
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
                self.mh.check(feedback.node.location,
                              feedback.message,
                              feedback.kind)
                ok_feasibility_checks.add(feedback)

    def create_counterexample(self, status, values):
        rv = [
            "example %s triggering error:" %
            self.n_ctyp.__class__.__name__.lower(),
            "  %s bad_potato {" % self.n_ctyp.name
        ]

        for n_component in self.n_ctyp.all_components():
            id_value = self.tr_component_value_name(n_component)
            id_valid = self.tr_component_valid_name(n_component)
            if status == "unknown" and (id_value not in values or
                                        id_valid not in values):
                rv.append("    %s = ???" % n_component.name)
            elif values.get(id_valid):
                rv.append("    %s = %s" %
                          (n_component.name,
                           self.value_to_trlc(n_component.n_typ,
                                              values[id_value])))
            else:
                rv.append("    /* %s is null */" % n_component.name)

        rv.append("  }")
        if status == "unknown":
            rv.append("/* note: counter-example is unreliable in this case */")
        return "\n".join(rv)

    def fraction_to_decimal_string(self, num, den):
        assert isinstance(num, int)
        assert isinstance(den, int) and den >= 1

        tmp = den
        if tmp > 2:
            while tmp > 1:
                if tmp % 2 == 0:
                    tmp = tmp // 2
                elif tmp % 5 == 0:
                    tmp = tmp // 5
                else:
                    return "%i / %u" % (num, den)

        rv = str(abs(num) // den)

        i = abs(num) % den
        j = den

        if i > 0:
            rv += "."
            while i > 0:
                i *= 10
                rv += str(i // j)
                i = i % j
        else:
            rv += ".0"

        if num < 0:
            return "-" + rv
        else:
            return rv

    def value_to_trlc(self, n_typ, value):
        assert isinstance(n_typ, Type)

        if isinstance(n_typ, Builtin_Integer):
            return str(value)

        elif isinstance(n_typ, Builtin_Decimal):
            if isinstance(value, Fraction):
                num, den = value.as_integer_ratio()
                if den >= 1:
                    return self.fraction_to_decimal_string(num, den)
                else:
                    return self.fraction_to_decimal_string(-num, -den)
            else:
                return "/* unable to generate precise value */"

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
            if value < 0:
                instance_id = value * -2 - 1
            else:
                instance_id = value * 2
            if n_typ.n_package is self.n_ctyp.n_package:
                return "%s_instance_%i" % (n_typ.name, instance_id)
            else:
                return "%s.%s_instance_%i" % (n_typ.n_package.name,
                                              n_typ.name,
                                              instance_id)

        elif isinstance(n_typ, Tuple_Type):
            parts = []
            for n_item in n_typ.iter_sequence():
                if isinstance(n_item, Composite_Component):
                    if n_item.optional and not value[n_item.name + ".valid"]:
                        parts.pop()
                        break
                    parts.append(
                        self.value_to_trlc(n_item.n_typ,
                                           value[n_item.name + ".value"]))

                else:
                    assert isinstance(n_item, Separator)
                    sep_text = {
                        "AT"        : "@",
                        "COLON"     : ":",
                        "SEMICOLON" : ";"
                    }.get(n_item.token.kind, n_item.token.value)
                    parts.append(sep_text)

            if n_typ.has_separators():
                return "".join(parts)
            else:
                return "(%s)" % ", ".join(parts)

        elif isinstance(n_typ, Array_Type):
            return "[%s]" % ", ".join(self.value_to_trlc(n_typ.element_type,
                                                         item)
                                      for item in value)

        else:  # pragma: no cover
            self.flag_unsupported(n_typ,
                                  "back-conversion from %s" % n_typ.name)

    def tr_component_value_name(self, n_component):
        return n_component.member_of.fully_qualified_name() + \
            "." + n_component.name + ".value"

    def tr_component_valid_name(self, n_component):
        return n_component.member_of.fully_qualified_name() + \
            "." + n_component.name + ".valid"

    def emit_tuple_constraints(self, n_tuple, s_sym):
        assert isinstance(n_tuple, Tuple_Type)
        assert isinstance(s_sym, smt.Constant)

        old_functional, self.functional = self.functional, True
        self.tuple_base[n_tuple] = s_sym

        constraints = []

        # The first tuple constraint is that all checks must have
        # passed, otherwise the tool would just error. An error in a
        # tuple is pretty much the same as a fatal in the enclosing
        # record.

        for n_check in n_tuple.iter_checks():
            if n_check.severity == "warning":
                continue
            # We do consider both fatal and errors to be sources of
            # truth here.
            c_value, _ = self.tr_expression(n_check.n_expr)
            constraints.append(c_value)

        # The secopnd tuple constraint is that once you get a null
        # field, all following fields must also be null.

        components = n_tuple.all_components()
        for i, component in enumerate(components):
            if component.optional:
                condition = smt.Boolean_Negation(
                    smt.Record_Access(s_sym,
                                      component.name + ".valid"))
                consequences = [
                    smt.Boolean_Negation(
                        smt.Record_Access(s_sym,
                                          c.name + ".valid"))
                    for c in components[i + 1:]
                ]
                if len(consequences) == 0:
                    break
                elif len(consequences) == 1:
                    consequence = consequences[0]
                else:
                    consequence = smt.Conjunction(*consequences)
                constraints.append(smt.Implication(condition, consequence))

        del self.tuple_base[n_tuple]
        self.functional = old_functional

        for cons in constraints:
            self.start.add_statement(smt.Assertion(cons))

    def tr_component_decl(self, n_component, gn_locals):
        assert isinstance(n_component, Composite_Component)
        assert isinstance(gn_locals, graph.Assumption)

        if isinstance(self.n_ctyp, Record_Type):
            frozen = self.n_ctyp.is_frozen(n_component)
        else:
            frozen = False

        id_value = self.tr_component_value_name(n_component)
        s_sort = self.tr_type(n_component.n_typ)
        s_sym  = smt.Constant(s_sort, id_value)
        if frozen:
            old_functional, self.functional = self.functional, True
            s_val, _ = self.tr_expression(
                self.n_ctyp.get_freezing_expression(n_component))
            self.functional = old_functional
        else:
            s_val = None
        s_decl = smt.Constant_Declaration(
            symbol   = s_sym,
            value    = s_val,
            comment  = "value for %s declared on %s" % (
                n_component.name,
                n_component.location.to_string()),
            relevant = True)
        gn_locals.add_statement(s_decl)
        self.constants[id_value] = s_sym

        if isinstance(n_component.n_typ, Tuple_Type):
            self.emit_tuple_constraints(n_component.n_typ, s_sym)

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
                  if n_component.optional and not frozen
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

        elif isinstance(n_type, Builtin_Decimal):
            return smt.BUILTIN_REAL

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

        elif isinstance(n_type, Tuple_Type):
            if n_type not in self.tuples:
                s_sort = smt.Record(n_type.n_package.name +
                                    "." + n_type.name)
                for n_component in n_type.all_components():
                    s_sort.add_component(n_component.name + ".value",
                                         self.tr_type(n_component.n_typ))
                    if n_component.optional:
                        s_sort.add_component(n_component.name + ".valid",
                                             smt.BUILTIN_BOOLEAN)
                self.tuples[n_type] = s_sort
                self.start.add_statement(
                    smt.Record_Declaration(
                        s_sort,
                        "tuple %s from %s" % (
                            n_type.name,
                            n_type.location.to_string())))

            return self.tuples[n_type]

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

        else:  # pragma: no cover
            self.flag_unsupported(n_type)

    def tr_check(self, n_check):
        assert isinstance(n_check, Check)

        # If the check belongs to a different type then we are looking
        # at a type extension. In this case we do not create checks
        # again, because if a check would failt it would already have
        # failed.
        if n_check.n_type is not self.n_ctyp:
            old_emit, self.emit_checks = self.emit_checks, False

        value, valid = self.tr_expression(n_check.n_expr)
        self.attach_validity_check(valid, n_check.n_expr)
        self.attach_feasability_check(value, n_check.n_expr)
        self.attach_assumption(value)

        if n_check.n_type is not self.n_ctyp:
            self.emit_checks = old_emit

    def tr_expression(self, n_expr):
        value = None

        if isinstance(n_expr, Name_Reference):
            return self.tr_name_reference(n_expr)

        elif isinstance(n_expr, Unary_Expression):
            return self.tr_unary_expression(n_expr)

        elif isinstance(n_expr, Binary_Expression):
            return self.tr_binary_expression(n_expr)

        elif isinstance(n_expr, Range_Test):
            return self.tr_range_test(n_expr)

        elif isinstance(n_expr, OneOf_Expression):
            return self.tr_oneof_test(n_expr)

        elif isinstance(n_expr, Conditional_Expression):
            if self.functional:
                return self.tr_conditional_expression_functional(n_expr)
            else:
                return self.tr_conditional_expression(n_expr)

        elif isinstance(n_expr, Null_Literal):
            return None, smt.Boolean_Literal(False)

        elif isinstance(n_expr, Boolean_Literal):
            value = smt.Boolean_Literal(n_expr.value)

        elif isinstance(n_expr, Integer_Literal):
            value = smt.Integer_Literal(n_expr.value)

        elif isinstance(n_expr, Decimal_Literal):
            value = smt.Real_Literal(n_expr.value)

        elif isinstance(n_expr, Enumeration_Literal):
            value = smt.Enumeration_Literal(self.tr_type(n_expr.typ),
                                            n_expr.value.name)

        elif isinstance(n_expr, String_Literal):
            value = smt.String_Literal(n_expr.value)

        elif isinstance(n_expr, Quantified_Expression):
            return self.tr_quantified_expression(n_expr)

        elif isinstance(n_expr, Field_Access_Expression):
            return self.tr_field_access_expression(n_expr)

        else:  # pragma: no cover
            self.flag_unsupported(n_expr)

        return value, smt.Boolean_Literal(True)

    def tr_name_reference(self, n_ref):
        assert isinstance(n_ref, Name_Reference)

        if isinstance(n_ref.entity, Composite_Component):
            if n_ref.entity.member_of in self.tuple_base:
                sym = self.tuple_base[n_ref.entity.member_of]
                if n_ref.entity.optional:
                    s_valid = smt.Record_Access(sym,
                                                n_ref.entity.name + ".valid")
                else:
                    s_valid = smt.Boolean_Literal(True)
                s_value = smt.Record_Access(sym,
                                            n_ref.entity.name + ".value")
                return s_value, s_valid

            else:
                id_value = self.tr_component_value_name(n_ref.entity)
                id_valid = self.tr_component_valid_name(n_ref.entity)
                return self.constants[id_value], self.constants[id_valid]

        else:
            assert isinstance(n_ref.entity, Quantified_Variable)
            if n_ref.entity in self.qe_vars:
                return self.qe_vars[n_ref.entity], smt.Boolean_Literal(True)
            else:
                return self.bound_vars[n_ref.entity], smt.Boolean_Literal(True)

    def tr_unary_expression(self, n_expr):
        assert isinstance(n_expr, Unary_Expression)

        operand_value, operand_valid = self.tr_expression(n_expr.n_operand)
        if not self.functional:
            self.attach_validity_check(operand_valid, n_expr.n_operand)

        sym_value = None

        if n_expr.operator == Unary_Operator.MINUS:
            if isinstance(n_expr.n_operand.typ, Builtin_Integer):
                sym_value = smt.Unary_Int_Arithmetic_Op("-",
                                                        operand_value)
            else:
                assert isinstance(n_expr.n_operand.typ, Builtin_Decimal)
                sym_value = smt.Unary_Real_Arithmetic_Op("-",
                                                         operand_value)

        elif n_expr.operator == Unary_Operator.PLUS:
            sym_value = operand_value

        elif n_expr.operator == Unary_Operator.LOGICAL_NOT:
            sym_value = smt.Boolean_Negation(operand_value)

        elif n_expr.operator == Unary_Operator.ABSOLUTE_VALUE:
            if isinstance(n_expr.n_operand.typ, Builtin_Integer):
                sym_value = smt.Unary_Int_Arithmetic_Op("abs",
                                                        operand_value)

            else:
                assert isinstance(n_expr.n_operand.typ, Builtin_Decimal)
                sym_value = smt.Unary_Real_Arithmetic_Op("abs",
                                                         operand_value)

        elif n_expr.operator == Unary_Operator.STRING_LENGTH:
            sym_value = smt.String_Length(operand_value)

        elif n_expr.operator == Unary_Operator.ARRAY_LENGTH:
            sym_value = smt.Sequence_Length(operand_value)

        elif n_expr.operator == Unary_Operator.CONVERSION_TO_DECIMAL:
            sym_value = smt.Conversion_To_Real(operand_value)

        elif n_expr.operator == Unary_Operator.CONVERSION_TO_INT:
            sym_value = smt.Conversion_To_Integer("rna", operand_value)

        else:
            self.mh.ice_loc(n_expr,
                            "unexpected unary operator %s" %
                            n_expr.operator.name)

        return self.create_return(n_expr, sym_value)

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

        elif n_expr.operator == Binary_Operator.LOGICAL_OR:
            return self.tr_op_or(n_expr)

        # The remaining operators always check for validity, so we can
        # obtain the values of both sides now.
        lhs_value, lhs_valid = self.tr_expression(n_expr.n_lhs)
        if not self.functional:
            self.attach_validity_check(lhs_valid, n_expr.n_lhs)
        rhs_value, rhs_valid = self.tr_expression(n_expr.n_rhs)
        if not self.functional:
            self.attach_validity_check(rhs_valid, n_expr.n_rhs)
        sym_value = None

        if n_expr.operator == Binary_Operator.LOGICAL_XOR:
            sym_value = smt.Exclusive_Disjunction(lhs_value, rhs_value)

        elif n_expr.operator in (Binary_Operator.PLUS,
                                 Binary_Operator.MINUS,
                                 Binary_Operator.TIMES,
                                 Binary_Operator.DIVIDE,
                                 Binary_Operator.REMAINDER):

            if isinstance(n_expr.n_lhs.typ, Builtin_String):
                assert n_expr.operator == Binary_Operator.PLUS
                sym_value = smt.String_Concatenation(lhs_value, rhs_value)

            elif isinstance(n_expr.n_lhs.typ, Builtin_Integer):
                if n_expr.operator in (Binary_Operator.DIVIDE,
                                       Binary_Operator.REMAINDER):
                    self.attach_int_division_check(rhs_value, n_expr)

                smt_op = {
                    Binary_Operator.PLUS      : "+",
                    Binary_Operator.MINUS     : "-",
                    Binary_Operator.TIMES     : "*",
                    Binary_Operator.DIVIDE    : "floor_div",
                    Binary_Operator.REMAINDER : "ada_remainder",
                }[n_expr.operator]

                sym_value = smt.Binary_Int_Arithmetic_Op(smt_op,
                                                         lhs_value,
                                                         rhs_value)

            else:
                assert isinstance(n_expr.n_lhs.typ, Builtin_Decimal)
                if n_expr.operator == Binary_Operator.DIVIDE:
                    self.attach_real_division_check(rhs_value, n_expr)

                smt_op = {
                    Binary_Operator.PLUS   : "+",
                    Binary_Operator.MINUS  : "-",
                    Binary_Operator.TIMES  : "*",
                    Binary_Operator.DIVIDE : "/",
                }[n_expr.operator]

                sym_value = smt.Binary_Real_Arithmetic_Op(smt_op,
                                                          lhs_value,
                                                          rhs_value)

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

        elif n_expr.operator == Binary_Operator.STRING_REGEX:
            rhs_evaluation = n_expr.n_rhs.evaluate(self.mh, None).value
            assert isinstance(rhs_evaluation, str)

            sym_value = smt.Function_Application(
                self.get_uf_matches(),
                lhs_value,
                smt.String_Literal(rhs_evaluation))

        elif n_expr.operator == Binary_Operator.INDEX:
            self.attach_index_check(lhs_value, rhs_value, n_expr)
            sym_value = smt.Sequence_Index(lhs_value, rhs_value)

        elif n_expr.operator == Binary_Operator.ARRAY_CONTAINS:
            sym_value = smt.Sequence_Contains(rhs_value, lhs_value)

        elif n_expr.operator == Binary_Operator.POWER:
            # LRM says that the exponent is always static and an
            # integer
            static_value = n_expr.n_rhs.evaluate(self.mh, None).value
            assert isinstance(static_value, int) and static_value >= 0

            if static_value == 0:
                if isinstance(n_expr.n_lhs.typ, Builtin_Integer):
                    sym_value = smt.Integer_Literal(1)
                else:
                    assert isinstance(n_expr.n_lhs.typ, Builtin_Decimal)
                    sym_value = smt.Real_Literal(1)

            else:
                sym_value = lhs_value
                for _ in range(1, static_value):
                    if isinstance(n_expr.n_lhs.typ, Builtin_Integer):
                        sym_value = smt.Binary_Int_Arithmetic_Op("*",
                                                                 sym_value,
                                                                 lhs_value)
                    else:
                        assert isinstance(n_expr.n_lhs.typ, Builtin_Decimal)
                        sym_value = smt.Binary_Real_Arithmetic_Op("*",
                                                                  sym_value,
                                                                  lhs_value)

        else:  # pragma: no cover
            self.flag_unsupported(n_expr, n_expr.operator.name)

        return self.create_return(n_expr, sym_value)

    def tr_range_test(self, n_expr):
        assert isinstance(n_expr, Range_Test)

        lhs_value, lhs_valid     = self.tr_expression(n_expr.n_lhs)
        self.attach_validity_check(lhs_valid, n_expr.n_lhs)
        lower_value, lower_valid = self.tr_expression(n_expr.n_lower)
        self.attach_validity_check(lower_valid, n_expr.n_lower)
        upper_value, upper_valid = self.tr_expression(n_expr.n_upper)
        self.attach_validity_check(upper_valid, n_expr.n_upper)

        sym_value = smt.Conjunction(
            smt.Comparison(">=", lhs_value, lower_value),
            smt.Comparison("<=", lhs_value, upper_value))

        return self.create_return(n_expr, sym_value)

    def tr_oneof_test(self, n_expr):
        assert isinstance(n_expr, OneOf_Expression)

        choices = []
        for n_choice in n_expr.choices:
            c_value, c_valid = self.tr_expression(n_choice)
            self.attach_validity_check(c_valid, n_choice)
            choices.append(c_value)

        negated_choices = [smt.Boolean_Negation(c)
                           for c in choices]

        # pylint: disable=consider-using-enumerate

        if len(choices) == 1:
            result = choices[0]
        elif len(choices) == 2:
            result = smt.Exclusive_Disjunction(choices[0], choices[1])
        else:
            assert len(choices) >= 3
            values = []
            for choice_id in range(len(choices)):
                sequence = []
                for other_id in range(len(choices)):
                    if other_id == choice_id:
                        sequence.append(choices[other_id])
                    else:
                        sequence.append(negated_choices[other_id])
                values.append(smt.Conjunction(*sequence))
            result = smt.Disjunction(*values)

        return self.create_return(n_expr, result)

    def tr_conditional_expression_functional(self, n_expr):
        assert isinstance(n_expr, Conditional_Expression)

        s_result, _ = self.tr_expression(n_expr.else_expr)
        for n_action in reversed(n_expr.actions):
            s_condition, _ = self.tr_expression(n_action.n_cond)
            s_true, _      = self.tr_expression(n_action.n_expr)
            s_result = smt.Conditional(s_condition, s_true, s_result)

        return self.create_return(n_expr, s_result)

    def tr_conditional_expression(self, n_expr):
        assert isinstance(n_expr, Conditional_Expression)
        assert not self.functional

        gn_end = graph.Node(self.graph)
        sym_result = smt.Constant(self.tr_type(n_expr.typ),
                                  self.new_temp_name())

        for n_action in n_expr.actions:
            test_value, test_valid = self.tr_expression(n_action.n_cond)
            self.attach_validity_check(test_valid, n_action.n_cond)
            current_start = self.start

            # Create path where action is true
            self.attach_assumption(test_value)
            res_value, res_valid = self.tr_expression(n_action.n_expr)
            self.attach_validity_check(res_valid, n_action.n_expr)
            self.attach_temp_declaration(n_action,
                                         sym_result,
                                         res_value)
            self.start.add_edge_to(gn_end)

            # Reset to test and proceed with the other actions
            self.start = current_start
            self.attach_assumption(smt.Boolean_Negation(test_value))

        # Finally execute the else part
        res_value, res_valid = self.tr_expression(n_expr.else_expr)
        self.attach_validity_check(res_valid, n_expr.else_expr)
        self.attach_temp_declaration(n_expr,
                                     sym_result,
                                     res_value)
        self.start.add_edge_to(gn_end)

        # And join
        self.start = gn_end
        return sym_result, smt.Boolean_Literal(True)

    def tr_op_implication(self, n_expr):
        assert isinstance(n_expr, Binary_Expression)
        assert n_expr.operator == Binary_Operator.LOGICAL_IMPLIES

        if self.functional:
            lhs_value, _ = self.tr_expression(n_expr.n_lhs)
            rhs_value, _ = self.tr_expression(n_expr.n_rhs)
            return self.create_return(n_expr,
                                      smt.Implication(lhs_value, rhs_value))

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

        if self.functional:
            lhs_value, _ = self.tr_expression(n_expr.n_lhs)
            rhs_value, _ = self.tr_expression(n_expr.n_rhs)
            return self.create_return(n_expr,
                                      smt.Conjunction(lhs_value, rhs_value))

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

    def tr_op_or(self, n_expr):
        assert isinstance(n_expr, Binary_Expression)
        assert n_expr.operator == Binary_Operator.LOGICAL_OR

        if self.functional:
            lhs_value, _ = self.tr_expression(n_expr.n_lhs)
            rhs_value, _ = self.tr_expression(n_expr.n_rhs)
            return self.create_return(n_expr,
                                      smt.Disjunction(lhs_value, rhs_value))

        lhs_value, lhs_valid = self.tr_expression(n_expr.n_lhs)
        # Emit VC for validity
        self.attach_validity_check(lhs_valid, n_expr.n_lhs)

        # Split into two paths.
        current_start = self.start
        sym_result = smt.Constant(smt.BUILTIN_BOOLEAN,
                                  self.new_temp_name())
        gn_end = graph.Node(self.graph)

        ### 1: LHS is true
        self.start = current_start
        self.attach_assumption(lhs_value)
        self.attach_temp_declaration(n_expr,
                                     sym_result,
                                     smt.Boolean_Literal(True))
        self.start.add_edge_to(gn_end)

        ### 2: LHS is not true
        self.start = current_start
        self.attach_assumption(smt.Boolean_Negation(lhs_value))
        rhs_value, rhs_valid = self.tr_expression(n_expr.n_rhs)
        self.attach_validity_check(rhs_valid, n_expr.n_rhs)
        self.attach_temp_declaration(n_expr,
                                     sym_result,
                                     rhs_value)
        self.start.add_edge_to(gn_end)

        # Join paths
        self.start = gn_end

        return sym_result, smt.Boolean_Literal(True)

    def tr_core_equality_tuple_component(self, n_component, lhs, rhs):
        assert isinstance(n_component, Composite_Component)
        assert isinstance(lhs, smt.Expression)
        assert isinstance(rhs, smt.Expression)

        value_lhs = smt.Record_Access(lhs,
                                      n_component.name + ".value")
        value_rhs = smt.Record_Access(rhs,
                                      n_component.name + ".value")
        valid_equal = self.tr_core_equality(n_component.n_typ,
                                            value_lhs,
                                            value_rhs)

        if not n_component.optional:
            return valid_equal

        valid_lhs = smt.Record_Access(lhs,
                                      n_component.name + ".valid")
        valid_rhs = smt.Record_Access(rhs,
                                      n_component.name + ".valid")

        return smt.Conjunction(
            smt.Comparison("=", valid_lhs, valid_rhs),
            smt.Implication(valid_lhs, valid_equal))

    def tr_core_equality(self, n_typ, lhs, rhs):
        assert isinstance(n_typ, Type)
        assert isinstance(lhs, smt.Expression)
        assert isinstance(rhs, smt.Expression)

        if isinstance(n_typ, Tuple_Type):
            parts = []
            for n_component in n_typ.all_components():
                parts.append(
                    self.tr_core_equality_tuple_component(n_component,
                                                          lhs,
                                                          rhs))

            if len(parts) == 0:
                return smt.Boolean_Literal(True)
            elif len(parts) == 1:
                return parts[0]
            else:
                result = smt.Conjunction(parts[0], parts[1])
                for part in parts[2:]:
                    result = smt.Conjunction(result, part)
                return result

        else:
            return smt.Comparison("=", lhs, rhs)

    def tr_op_equality(self, n_expr):
        assert isinstance(n_expr, Binary_Expression)
        assert n_expr.operator in (Binary_Operator.COMP_EQ,
                                   Binary_Operator.COMP_NEQ)

        lhs_value, lhs_valid = self.tr_expression(n_expr.n_lhs)
        rhs_value, rhs_valid = self.tr_expression(n_expr.n_rhs)

        if lhs_value is None:
            comp_typ = n_expr.n_rhs.typ
        else:
            comp_typ = n_expr.n_lhs.typ

        if lhs_valid.is_static_true() and rhs_valid.is_static_true():
            # Simplified form, this is just x == y
            result = self.tr_core_equality(comp_typ,
                                           lhs_value,
                                           rhs_value)

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
                                self.tr_core_equality(comp_typ,
                                                      lhs_value,
                                                      rhs_value)))

        if n_expr.operator == Binary_Operator.COMP_NEQ:
            result = smt.Boolean_Negation(result)

        return self.create_return(n_expr, result)

    def tr_quantified_expression(self, n_expr):
        assert isinstance(n_expr, Quantified_Expression)

        # Nested quantifiers are not supported yet
        if self.functional:  # pragma: no cover
            self.flag_unsupported(n_expr,
                                  "functional evaluation of quantifier")

        # TRLC quantifier
        #   (forall x in arr_name => body)
        #
        # SMT quantifier
        #   (forall ((i Int))
        #     (=> (and (>= i 0) (< i (seq.len arr_name)))
        #         (... (seq.nth arr_name i) ... )))
        #
        # There is an alternative which is:
        #   (forall ((element ElementSort))
        #     (=> (seq.contains arr_name (seq.unit element))
        #         (... element ...)
        #
        # However it looks like for CVC5 at least this generates more
        # unknown and less unsat if a check depends on the explicit
        # value of some sequence member.

        # Evaluate subject first and creat a null check
        s_subject_value, s_subject_valid = \
            self.tr_name_reference(n_expr.n_source)
        self.attach_validity_check(s_subject_valid, n_expr.n_source)

        # Create validity checks for the body. We do this by creating
        # a new branch and eliminating the quantifier; pretending it's
        # a forall (since we want to show that for all evaluations
        # it's valid).
        current_start = self.start
        self.attach_empty_assumption()
        src_typ = n_expr.n_source.typ
        assert isinstance(src_typ, Array_Type)
        s_qe_index = smt.Constant(smt.BUILTIN_INTEGER,
                                  self.new_temp_name())
        self.start.add_statement(
            smt.Constant_Declaration(
                symbol   = s_qe_index,
                comment  = ("quantifier elimination (index) for %s at %s" %
                            (n_expr.to_string(),
                             n_expr.location.to_string()))))
        self.start.add_statement(
            smt.Assertion(smt.Comparison(">=",
                                         s_qe_index,
                                         smt.Integer_Literal(0))))
        self.start.add_statement(
            smt.Assertion(
                smt.Comparison("<",
                               s_qe_index,
                               smt.Sequence_Length(s_subject_value))))
        s_qe_sym = smt.Constant(self.tr_type(src_typ.element_type),
                                self.new_temp_name())
        self.start.add_statement(
            smt.Constant_Declaration(
                symbol   = s_qe_sym,
                value    = smt.Sequence_Index(s_subject_value, s_qe_index),
                comment  = ("quantifier elimination (symbol) for %s at %s" %
                            (n_expr.to_string(),
                             n_expr.location.to_string()))))
        self.qe_vars[n_expr.n_var] = s_qe_sym

        _, b_valid = self.tr_expression(n_expr.n_expr)
        self.attach_validity_check(b_valid, n_expr.n_expr)

        self.start = current_start
        del self.qe_vars[n_expr.n_var]

        # We have now shown that any path in the quantifier cannot
        # raise exception. Asserting the actual value of the
        # quantifier is more awkward.

        s_q_idx = smt.Bound_Variable(smt.BUILTIN_INTEGER,
                                     self.new_temp_name())
        s_q_sym = smt.Sequence_Index(s_subject_value, s_q_idx)
        self.bound_vars[n_expr.n_var] = s_q_sym

        temp, self.functional = self.functional, True
        b_value, _ = self.tr_expression(n_expr.n_expr)
        self.functional = temp

        bounds_expr = smt.Conjunction(
            smt.Comparison(">=",
                           s_q_idx,
                           smt.Integer_Literal(0)),
            smt.Comparison("<",
                           s_q_idx,
                           smt.Sequence_Length(s_subject_value)))
        if n_expr.universal:
            value = smt.Quantifier(
                "forall",
                [s_q_idx],
                smt.Implication(bounds_expr, b_value))
        else:
            value = smt.Quantifier(
                "exists",
                [s_q_idx],
                smt.Conjunction(bounds_expr, b_value))

        return value, smt.Boolean_Literal(True)

    def tr_field_access_expression(self, n_expr):
        assert isinstance(n_expr, Field_Access_Expression)

        prefix_value, prefix_valid = self.tr_expression(n_expr.n_prefix)
        self.attach_validity_check(prefix_valid, n_expr.n_prefix)

        field_value = smt.Record_Access(prefix_value,
                                        n_expr.n_field.name + ".value")
        if n_expr.n_field.optional:
            field_valid = smt.Record_Access(prefix_value,
                                            n_expr.n_field.name + ".valid")
        else:
            field_valid = smt.Boolean_Literal(True)

        return field_value, field_valid
