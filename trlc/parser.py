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

import re

from trlc.lexer import Token, Lexer, create_lexer
from trlc.errors import Message_Handler
from trlc import ast


class Parser:
    COMPARISON_OPERATOR = ("==", "!=", "<", "<=", ">", ">=")
    ADDING_OPERATOR = ("+", "-")
    MULTIPLYING_OPERATOR = ("*", "/", "%")

    def __init__(self, mh, stab, file_name, lint_mode):
        assert isinstance(mh, Message_Handler)
        assert isinstance(stab, ast.Symbol_Table)
        assert isinstance(file_name, str)
        assert isinstance(lint_mode, bool)
        self.mh        = mh
        self.lint_mode = lint_mode
        self.lexer     = create_lexer(mh, file_name)
        self.stab      = stab
        self.pkg       = None
        self.raw_deps  = []
        self.deps      = []
        self.imports   = set()

        self.ct = None
        self.nt = self.lexer.token()

        self.builtin_bool = stab.table["Boolean"]
        self.builtin_int  = stab.table["Integer"]
        self.builtin_str  = stab.table["String"]

        self.section = []
        self.default_scope = ast.Scope()
        self.default_scope.push(self.stab)

    def advance(self):
        self.ct = self.nt
        self.nt = self.lexer.token()

    def peek(self, kind):
        assert kind in Token.KIND
        return self.nt is not None and self.nt.kind == kind

    def peek_eof(self):
        return self.nt is None

    def peek_kw(self, value):
        assert value in Lexer.KEYWORDS
        return self.peek("KEYWORD") and self.nt.value == value

    def match(self, kind):
        assert kind in Token.KIND
        if self.nt is None:
            self.mh.error(self.ct.location,
                          "expected %s, encountered end-of-file instead" %
                          kind)
        elif self.nt.kind != kind:
            self.mh.error(self.nt.location,
                          "expected %s, encountered %s instead" %
                          (kind, self.nt.kind))
        self.advance()

    def match_eof(self):
        if self.nt is not None:
            self.mh.error(self.nt.location,
                          "expected end-of-file, encountered %s instead" %
                          self.nt.kind)

    def match_kw(self, value):
        assert value in Lexer.KEYWORDS
        if self.nt is None:
            self.mh.error(self.ct.location,
                          "expected %s, encountered end-of-file instead" %
                          value)
        elif self.nt.kind != "KEYWORD":
            self.mh.error(self.nt.location,
                          "expected %s, encountered %s instead" %
                          (value, self.nt.kind))
        elif self.nt.value != value:
            self.mh.error(self.nt.location,
                          "expected %s, encountered %s instead" %
                          (value, self.nt.value))
        self.advance()

    def parse_described_name(self):
        self.match("IDENTIFIER")
        name = self.ct

        if self.peek("STRING"):
            self.match("STRING")
            return name, self.ct.value
        else:
            return name, None

    def parse_qualified_name(self,
                             scope,
                             required_subclass=None,
                             match_ident=True):
        assert isinstance(scope, ast.Scope)
        assert isinstance(required_subclass, type)
        assert isinstance(match_ident, bool)

        if match_ident:
            self.match("IDENTIFIER")
        sym = scope.lookup(self.mh, self.ct)

        if isinstance(sym, ast.Package):
            if sym != self.pkg and sym.name not in self.imports:
                self.mh.error(self.ct.location,
                              "package must be imported before use")
            self.match("DOT")
            self.match("IDENTIFIER")
            return sym.symbols.lookup(self.mh, self.ct, required_subclass)
        else:
            return scope.lookup(self.mh, self.ct, required_subclass)

    def parse_type_declaration(self):
        if self.peek_kw("enum"):
            self.parse_enum_declaration()
        else:
            self.parse_record_declaration()

    def parse_enum_declaration(self):
        self.match_kw("enum")
        name, description = self.parse_described_name()

        enum = ast.Enumeration_Type(name        = name.value,
                                    description = description,
                                    location    = name.location)
        self.pkg.symbols.register(self.mh, enum)

        self.match("C_BRA")
        while not self.peek("C_KET"):
            name, description = self.parse_described_name()
            lit = ast.Enumeration_Literal_Spec(name        = name.value,
                                               description = description,
                                               location    = name.location,
                                               enum        = enum)
            enum.literals.register(self.mh, lit)
        self.match("C_KET")

    def parse_record_declaration(self):
        self.match_kw("type")
        name, description = self.parse_described_name()

        if self.peek_kw("extends"):
            self.match_kw("extends")
            root_record = self.parse_qualified_name(self.default_scope,
                                                    ast.Record_Type)
        else:
            root_record = None

        record = ast.Record_Type(name        = name.value,
                                 description = description,
                                 location    = name.location,
                                 parent      = root_record)
        self.pkg.symbols.register(self.mh, record)

        self.match("C_BRA")
        while not self.peek("C_KET"):
            c_name, c_descr = self.parse_described_name()
            if self.peek_kw("optional"):
                self.match_kw("optional")
                c_optional = True
            else:
                c_optional = False
            c_typ = self.parse_qualified_name(self.default_scope,
                                              ast.Type)

            if self.peek("S_BRA"):
                self.match("S_BRA")
                self.match("INTEGER")
                a_lo = self.ct.value
                self.match("RANGE")
                a_loc = self.ct.location
                if self.peek("INTEGER"):
                    self.match("INTEGER")
                    a_hi = self.ct.value
                    if a_lo > a_hi:
                        self.mh.error(self.ct.location,
                                      "upper bound must be at least %u" % a_lo,
                                      fatal = False)
                    elif a_hi == 0:
                        self.mh.error(self.ct.location,
                                      "this array makes no sense",
                                      fatal = False)
                    elif a_hi == 1 and a_lo == 1:
                        self.mh.warning(a_loc,
                                        "array of fixed size 1 "
                                        "should not be an array")
                    elif a_hi == 1 and a_lo == 0:
                        self.mh.warning(a_loc,
                                        "consider making this array an"
                                        " optional %s" % c_typ.name)

                elif self.peek("OPERATOR") and self.nt.value == "*":
                    self.match("OPERATOR")
                    a_hi = None
                else:
                    self.mh.error(self.nt.location,
                                  "expected INTEGER or * for upper bound")
                self.match("S_KET")
                c_typ = ast.Array_Type(location     = a_loc,
                                       element_type = c_typ,
                                       lower_bound  = a_lo,
                                       upper_bound  = a_hi)

            comp = ast.Record_Component(name        = c_name.value,
                                        description = c_descr,
                                        location    = c_name.location,
                                        record      = record,
                                        typ         = c_typ,
                                        optional    = c_optional)
            record.components.register(self.mh, comp)

        self.match("C_KET")

    def parse_expression(self, scope):
        assert isinstance(scope, ast.Scope)

        n_lhs = self.parse_relation(scope)

        if self.peek_kw("and"):
            while self.peek_kw("and"):
                self.match_kw("and")
                t_op  = self.ct
                n_rhs = self.parse_relation(scope)
                n_lhs = ast.Binary_Expression(
                    mh       = self.mh,
                    location = t_op.location,
                    typ      = self.builtin_bool,
                    operator = ast.Binary_Operator.LOGICAL_AND,
                    n_lhs    = n_lhs,
                    n_rhs    = n_rhs)

        elif self.peek_kw("or"):
            while self.peek_kw("or"):
                self.match_kw("or")
                t_op  = self.ct
                n_rhs = self.parse_relation(scope)
                n_lhs = ast.Binary_Expression(
                    mh       = self.mh,
                    location = t_op.location,
                    typ      = self.builtin_bool,
                    operator = ast.Binary_Operator.LOGICAL_OR,
                    n_lhs    = n_lhs,
                    n_rhs    = n_rhs)

        elif self.peek_kw("xor"):
            self.match_kw("xor")
            t_op  = self.ct
            n_rhs = self.parse_relation(scope)
            n_lhs = ast.Binary_Expression(
                mh       = self.mh,
                location = t_op.location,
                typ      = self.builtin_bool,
                operator = ast.Binary_Operator.LOGICAL_XOR,
                n_lhs    = n_lhs,
                n_rhs    = n_rhs)

        elif self.peek_kw("implies"):
            self.match_kw("implies")
            t_op  = self.ct
            n_rhs = self.parse_relation(scope)
            n_lhs = ast.Binary_Expression(
                mh       = self.mh,
                location = t_op.location,
                typ      = self.builtin_bool,
                operator = ast.Binary_Operator.LOGICAL_IMPLIES,
                n_lhs    = n_lhs,
                n_rhs    = n_rhs)

        return n_lhs

    def parse_relation(self, scope):
        assert isinstance(scope, ast.Scope)
        relop_mapping = {"==" : ast.Binary_Operator.COMP_EQ,
                         "!=" : ast.Binary_Operator.COMP_NEQ,
                         "<"  : ast.Binary_Operator.COMP_LT,
                         "<=" : ast.Binary_Operator.COMP_LEQ,
                         ">"  : ast.Binary_Operator.COMP_GT,
                         ">=" : ast.Binary_Operator.COMP_GEQ}
        assert set(relop_mapping) == set(Parser.COMPARISON_OPERATOR)

        n_lhs = self.parse_simple_expression(scope)

        if self.peek("OPERATOR") and \
           self.nt.value in Parser.COMPARISON_OPERATOR:
            self.match("OPERATOR")
            t_op  = self.ct
            n_rhs = self.parse_simple_expression(scope)
            return ast.Binary_Expression(
                mh       = self.mh,
                location = t_op.location,
                typ      = self.builtin_bool,
                operator = relop_mapping[t_op.value],
                n_lhs    = n_lhs,
                n_rhs    = n_rhs)

        elif self.peek_kw("not") or self.peek_kw("in"):
            if self.peek_kw("not"):
                self.match_kw("not")
                t_not = self.ct
            else:
                t_not = None

            self.match_kw("in")
            t_in = self.ct

            n_a = self.parse_simple_expression(scope)
            if self.peek("RANGE"):
                self.match("RANGE")
                n_b = self.parse_simple_expression(scope)
                rv  = ast.Range_Test(
                    mh       = self.mh,
                    location = t_in.location,
                    typ      = self.builtin_bool,
                    n_lhs    = n_lhs,
                    n_lower  = n_a,
                    n_upper  = n_b)

            else:
                rv = ast.Binary_Expression(
                    mh       = self.mh,
                    location = t_in.location,
                    typ      = self.builtin_bool,
                    operator = ast.Binary_Operator.STRING_CONTAINS,
                    n_lhs    = n_lhs,
                    n_rhs    = n_a)

            if t_not is not None:
                rv = ast.Unary_Expression(
                    mh        = self.mh,
                    location  = t_not.location,
                    typ       = self.builtin_bool,
                    operator  = ast.Unary_Operator.LOGICAL_NOT,
                    n_operand = rv)

            return rv

        else:
            return n_lhs

    def parse_simple_expression(self, scope):
        assert isinstance(scope, ast.Scope)
        un_add_map = {"+" : ast.Unary_Operator.PLUS,
                      "-" : ast.Unary_Operator.MINUS}
        bin_add_map = {"+" : ast.Binary_Operator.PLUS,
                       "-" : ast.Binary_Operator.MINUS}
        assert set(un_add_map) == set(Parser.ADDING_OPERATOR)
        assert set(bin_add_map) == set(Parser.ADDING_OPERATOR)

        if self.peek("OPERATOR") and \
           self.nt.value in Parser.ADDING_OPERATOR:
            self.match("OPERATOR")
            t_unary = self.ct
            has_explicit_brackets = self.peek("BRA")
        else:
            t_unary = None

        n_lhs = self.parse_term(scope)
        if t_unary:
            if self.lint_mode and \
               isinstance(n_lhs, ast.Binary_Expression) and \
               not has_explicit_brackets:
                self.mh.warning(t_unary.location,
                                "expression means -(%s), place explicit "
                                "brackets to clarify intent" %
                                n_lhs.to_string())
            n_lhs = ast.Unary_Expression(
                mh        = self.mh,
                location  = t_unary.location,
                typ       = n_lhs.typ,
                operator  = un_add_map[t_unary.value],
                n_operand = n_lhs)

        while self.peek("OPERATOR") and \
              self.nt.value in Parser.ADDING_OPERATOR:
            self.match("OPERATOR")
            t_op  = self.ct
            n_rhs = self.parse_term(scope)
            n_lhs = ast.Binary_Expression(
                mh       = self.mh,
                location = t_op.location,
                typ      = n_lhs.typ,
                operator = bin_add_map[t_op.value],
                n_lhs    = n_lhs,
                n_rhs    = n_rhs)

        return n_lhs

    def parse_term(self, scope):
        assert isinstance(scope, ast.Scope)
        mul_map = {"*" : ast.Binary_Operator.TIMES,
                   "/" : ast.Binary_Operator.DIVIDE,
                   "%" : ast.Binary_Operator.REMAINDER}
        assert set(mul_map) == set(Parser.MULTIPLYING_OPERATOR)

        n_lhs = self.parse_factor(scope)
        while self.peek("OPERATOR") and \
              self.nt.value in Parser.MULTIPLYING_OPERATOR:
            self.match("OPERATOR")
            t_op  = self.ct
            n_rhs = self.parse_factor(scope)
            n_lhs = ast.Binary_Expression(
                mh       = self.mh,
                location = t_op.location,
                typ      = n_lhs.typ,
                operator = mul_map[t_op.value],
                n_lhs    = n_lhs,
                n_rhs    = n_rhs)

        return n_lhs

    def parse_factor(self, scope):
        assert isinstance(scope, ast.Scope)

        if self.peek_kw("not"):
            self.match_kw("not")
            t_op      = self.ct
            n_operand = self.parse_primary(scope)
            return ast.Unary_Expression(
                mh        = self.mh,
                location  = t_op.location,
                typ       = self.builtin_bool,
                operator  = ast.Unary_Operator.LOGICAL_NOT,
                n_operand = n_operand)

        elif self.peek_kw("abs"):
            self.match_kw("abs")
            t_op      = self.ct
            n_operand = self.parse_primary(scope)
            return ast.Unary_Expression(
                mh        = self.mh,
                location  = t_op.location,
                typ       = self.builtin_int,
                operator  = ast.Unary_Operator.ABSOLUTE_VALUE,
                n_operand = n_operand)

        else:
            n_lhs = self.parse_primary(scope)
            if self.peek("OPERATOR") and self.nt.value == "**":
                self.match("OPERATOR")
                t_op  = self.ct
                n_rhs = self.parse_primary(scope)
                n_rhs.evaluate(self.mh, None)
                n_lhs = ast.Binary_Expression(
                    mh       = self.mh,
                    location = t_op.location,
                    typ      = self.builtin_int,
                    operator = ast.Binary_Operator.POWER,
                    n_lhs    = n_lhs,
                    n_rhs    = n_rhs)
            return n_lhs

    def parse_primary(self, scope):
        assert isinstance(scope, ast.Scope)

        if self.peek("INTEGER"):
            self.match("INTEGER")
            return ast.Integer_Literal(self.ct, self.builtin_int)

        elif self.peek("STRING"):
            self.match("STRING")
            return ast.String_Literal(self.ct, self.builtin_str)

        elif self.peek_kw("null"):
            self.match_kw("null")
            return ast.Null_Literal(self.ct)

        elif self.peek("BRA"):
            self.match("BRA")
            if self.peek_kw("forall"):
                rv = self.parse_quantified_expression(scope)
            elif self.peek_kw("if"):
                rv = self.parse_conditional_expression(scope)
            else:
                rv = self.parse_expression(scope)
            self.match("KET")
            return rv

        else:
            return self.parse_name(scope)

    def parse_quantified_expression(self, scope):
        assert isinstance(scope, ast.Scope)

        self.match_kw("forall")
        loc = self.ct.location
        self.match("IDENTIFIER")
        t_qv = self.ct
        if scope.contains(t_qv.value):
            pdef = scope.lookup(self.mh, t_qv)
            self.mh.error(t_qv.location,
                          "shadows %s %s from %s" %
                          (pdef.__class__.__name__,
                           pdef.name,
                           pdef.location.to_string(False)))
        self.match_kw("in")
        self.match("IDENTIFIER")
        field = scope.lookup(self.mh, self.ct, ast.Record_Component)
        n_source = ast.Name_Reference(self.ct.location,
                                      field)
        if not isinstance(field.typ, ast.Array_Type):
            self.mh.error(self.ct.location,
                          "you can only quantify over arrays")
        n_var = ast.Quantified_Variable(t_qv.value,
                                        t_qv.location,
                                        field.typ.element_type)
        self.match("ARROW")

        new_table = ast.Symbol_Table()
        new_table.register(self.mh, n_var)
        scope.push(new_table)
        n_expr = self.parse_expression(scope)
        scope.pop()

        return ast.Quantified_Expression(mh         = self.mh,
                                         location   = loc,
                                         typ        = self.builtin_bool,
                                         n_variable = n_var,
                                         n_source   = n_source,
                                         n_expr     = n_expr)

    def parse_conditional_expression(self, scope):
        assert isinstance(scope, ast.Scope)

        self.match_kw("if")
        t_if = self.ct
        if_cond = self.parse_expression(scope)
        self.match_kw("then")
        if_expr = self.parse_expression(scope)
        if_action = ast.Action(self.mh, t_if, if_cond, if_expr)

        rv = ast.Conditional_Expression(location  = t_if.location,
                                        if_action = if_action)

        while self.peek_kw("elsif"):
            self.match_kw("elsif")
            t_elsif = self.ct
            elsif_cond = self.parse_expression(scope)
            self.match_kw("then")
            elsif_expr = self.parse_expression(scope)
            elsif_action = ast.Action(self.mh, t_elsif, elsif_cond, elsif_expr)
            rv.add_elsif(self.mh, elsif_action)

        self.match_kw("else")
        else_expr = self.parse_expression(scope)
        rv.set_else_part(self.mh, else_expr)

        return rv

    def parse_builtin(self, scope, n_name, t_name):
        assert isinstance(scope, ast.Scope)
        assert isinstance(n_name, ast.Builtin_Function)
        assert isinstance(t_name, Token)

        # Lint: complain about old functions
        if self.lint_mode and n_name.deprecated:
            self.mh.warning(
                t_name.location,
                "deprecated feature, please use function %s instead" %
                n_name.name.replace("trlc:", ""))

        # Parse the arguments.
        parameters = []
        self.match("BRA")
        while not self.peek("KET"):
            parameters.append(self.parse_expression(scope))
            if self.peek("COMMA"):
                self.match("COMMA")
            else:
                break
        self.match("KET")

        # Enforce arity
        if n_name.arity != len(parameters):
            self.mh.error(t_name.location,
                          "function %requires %u parameters" %
                          n_name.arity)

        # Enforce types
        if n_name.name in ("len", "trlc:len"):
            if parameters[0].typ == self.builtin_str:
                return ast.Unary_Expression(
                    mh        = self.mh,
                    location  = t_name.location,
                    typ       = self.builtin_int,
                    operator  = ast.Unary_Operator.STRING_LENGTH,
                    n_operand = parameters[0])
            else:
                return ast.Unary_Expression(
                    mh        = self.mh,
                    location  = t_name.location,
                    typ       = self.builtin_int,
                    operator  = ast.Unary_Operator.ARRAY_LENGTH,
                    n_operand = parameters[0])

        elif n_name.name in ("startswith",
                             "endswith",
                             "trlc:startswith",
                             "trlc:endswith"):
            return ast.Binary_Expression(
                mh       = self.mh,
                location = t_name.location,
                typ      = self.builtin_bool,
                operator = (ast.Binary_Operator.STRING_STARTSWITH
                            if "startswith" in n_name.name
                            else ast.Binary_Operator.STRING_ENDSWITH),
                n_lhs    = parameters[0],
                n_rhs    = parameters[1])

        elif n_name.name in ("matches", "trlc:matches"):
            parameters[1].ensure_type(self.mh, ast.Builtin_String)
            try:
                # TODO: Fix scope for evaluate()
                value = parameters[1].evaluate(self.mh, None)
                assert isinstance(value.typ, ast.Builtin_String)
                re.compile(value.value)
            except re.error as err:
                self.mh.error(value.location,
                              str(err))
            return ast.Binary_Expression(
                mh       = self.mh,
                location = t_name.location,
                typ      = self.builtin_bool,
                operator = ast.Binary_Operator.STRING_REGEX,
                n_lhs    = parameters[0],
                n_rhs    = parameters[1])

        else:
            self.mh.ice_loc(t_name.location,
                            "unexpected builtin")

    def parse_name(self, scope):
        # This is a bit more complex. The grammar is:
        #
        # qualified_name ::= [ IDENTIFIER_package_name '.' ] IDENTIFIER_name
        #
        # name ::= qualified_name
        #        | qualified_name ['.' IDENTIFIER_literal]
        #        | name '[' expression ']'
        #        | IDENTIFIER_builtin_function '(' parameter_list ')'
        #        | BUILTIN '(' parameter_list ')'
        #
        # parameter_list ::= expression { ',' expression }
        assert isinstance(scope, ast.Scope)

        if self.peek("BUILTIN"):
            # Legacy builtin function call. The lookup in the root
            # scope is not an error.
            self.match("BUILTIN")
            n_name = self.stab.lookup(self.mh, self.ct, ast.Builtin_Function)
            return self.parse_builtin(scope, n_name, self.ct)

        else:
            self.match("IDENTIFIER")

            if self.peek("S_BRA"):
                # Must be an array index on a record field
                #        | name '[' expression ']'
                n_name = scope.lookup(self.mh, self.ct, ast.Entity)
                if not isinstance(n_name.typ, ast.Array_Type):
                    self.mh.error(n_name.location,
                                  "is not of an array type")
                n_lhs = ast.Name_Reference(location = self.ct.location,
                                           entity   = n_name)

                self.match("S_BRA")
                t_bracket = self.ct
                n_index = self.parse_expression(scope)
                self.match("S_KET")
                return ast.Binary_Expression(
                    mh       = self.mh,
                    location = t_bracket.location,
                    typ      = n_name.typ.element_type,
                    operator = ast.Binary_Operator.INDEX,
                    n_lhs    = n_lhs,
                    n_rhs    = n_index)

            elif self.peek("BRA"):
                # Must be a builtin call
                #        | IDENTIFIER_builtin_function '(' parameter_list ')'
                # The lookup in the root scope is not an error. We do
                # this to avoid finding record fields that happen to
                # have the same name.
                n_name = self.stab.lookup(self.mh,
                                          self.ct,
                                          ast.Builtin_Function)
                return self.parse_builtin(scope, n_name, self.ct)

            else:
                # Must be a qualified name or enumeration
                # name ::= qualified_name
                #        | qualified_name ['.' IDENTIFIER_literal]
                n_name = self.parse_qualified_name(
                    scope             = scope,
                    required_subclass = ast.Entity,
                    match_ident       = False)
                t_name = self.ct

                if isinstance(n_name, ast.Enumeration_Type):
                    # If the (qualified) name refers to a enum, then
                    # we have to narrow it down to a literal.
                    self.match("DOT")
                    self.match("IDENTIFIER")
                    lit = n_name.literals.lookup(self.mh,
                                                 self.ct,
                                                 ast.Enumeration_Literal_Spec)
                    return ast.Enumeration_Literal(location = self.ct.location,
                                                   literal  = lit)

                else:
                    # Otherwise we're done
                    return ast.Name_Reference(location = t_name.location,
                                              entity   = n_name)

    def parse_check_block(self):
        self.match_kw("checks")
        self.match("IDENTIFIER")
        record = self.pkg.symbols.lookup(self.mh, self.ct, ast.Record_Type)
        scope = ast.Scope()
        scope.push(self.stab)
        scope.push(self.pkg.symbols)
        scope.push(record.components)
        self.match("C_BRA")
        while not self.peek("C_KET"):
            c_expr = self.parse_expression(scope)

            self.match("COMMA")
            if self.peek("KEYWORD"):
                self.match("KEYWORD")
                if self.ct.value not in ("warning", "error", "fatal"):
                    self.mh.error(self.ct.location,
                                  "expected warning|error|fatal")
                c_sev = self.ct.value
            else:
                c_sev = "error"

            self.match("STRING")
            t_msg = self.ct

            if self.peek("COMMA"):
                self.match("COMMA")
                self.match("IDENTIFIER")
                c_anchor = record.components.lookup(self.mh,
                                                    self.ct,
                                                    ast.Record_Component)
            else:
                c_anchor = None

            n_check = ast.Check(n_record  = record,
                                n_expr    = c_expr,
                                n_anchor  = c_anchor,
                                severity  = c_sev,
                                t_message = t_msg)
            record.add_check(n_check)

            assert scope.size() == 3

        self.match("C_KET")

    def parse_section_declaration(self):
        self.match_kw("section")
        self.match("STRING")
        if self.section:
            sec = ast.Section(name     = self.ct.value,
                              location = self.ct.location,
                              parent   = self.section[-1])
        else:
            sec = ast.Section(name     = self.ct.value,
                              location = self.ct.location,
                              parent   = None)
        self.section.append(sec)
        self.match("C_BRA")
        while not self.peek("C_KET"):
            self.parse_trlc_entry()
        self.match("C_KET")
        self.section.pop()

    def parse_boolean(self):
        self.match("KEYWORD")
        if self.ct.value in ("true", "false"):
            return ast.Boolean_Literal(self.ct, self.builtin_bool)
        else:
            self.mh.error(self.ct.location,
                          "expected boolean literal (true or false)")

    def parse_value(self, typ):
        assert isinstance(typ, ast.Type)

        if isinstance(typ, ast.Builtin_Integer):
            self.match("INTEGER")
            return ast.Integer_Literal(self.ct, self.builtin_int)

        elif isinstance(typ, ast.Builtin_String):
            self.match("STRING")
            return ast.String_Literal(self.ct, self.builtin_str)

        elif isinstance(typ, ast.Builtin_Boolean):
            return self.parse_boolean()

        elif isinstance(typ, ast.Array_Type):
            self.match("S_BRA")
            rv = ast.Array_Aggregate(self.ct.location,
                                     typ)
            while not self.peek("S_KET"):
                rv.append(self.parse_value(typ.element_type))
                if self.peek("COMMA"):
                    self.match("COMMA")
            self.match("S_KET")
            # TODO: Check length

            return rv

        elif isinstance(typ, ast.Enumeration_Type):
            enum = self.parse_qualified_name(self.default_scope,
                                             ast.Enumeration_Type)
            if enum != typ:
                self.mh.error(self.ct.location,
                              "expected %s" % typ.name)
            self.match("DOT")
            self.match("IDENTIFIER")
            lit = enum.literals.lookup(self.mh,
                                       self.ct,
                                       ast.Enumeration_Literal_Spec)
            return ast.Enumeration_Literal(self.ct.location,
                                           lit)

        elif isinstance(typ, ast.Record_Type):
            # TODO: Defer name resolution?
            # TODO: Type check
            self.match("IDENTIFIER")
            t_name = self.ct
            if self.peek("DOT"):
                self.match("DOT")
                self.match("IDENTIFIER")
                the_pkg = self.stab.lookup(self.mh, t_name, ast.Package)
                if the_pkg != self.pkg and the_pkg.name not in self.imports:
                    self.mh.error(self.ct.location,
                                  "package must be imported before use")
                t_name = self.ct
            else:
                the_pkg = self.pkg

            rv = ast.Record_Reference(t_name, typ, the_pkg)
            if the_pkg.symbols.contains(t_name.value):
                rv.target = the_pkg.symbols.lookup(self.mh,
                                                   t_name,
                                                   ast.Record_Object)
                if not rv.target.e_typ.is_subclass_of(typ):
                    self.mh.error(t_name.location,
                                  "incorrect type, expected %s but %s is %s" %
                                  (typ.name,
                                   rv.name,
                                   rv.target.e_typ.name))

            return rv

        else:
            self.mh.ice_loc(self.ct.location,
                            "logic error: unexpected type %s" %
                            typ.__class__.__name__)

    def parse_record_object_declaration(self):
        r_typ = self.parse_qualified_name(self.default_scope,
                                          ast.Record_Type)
        self.match("IDENTIFIER")
        obj = ast.Record_Object(
            name     = self.ct.value,
            location = self.ct.location,
            e_typ    = r_typ,
            section  = self.section[-1] if self.section else None)
        self.pkg.symbols.register(self.mh, obj)
        self.match("C_BRA")
        while not self.peek("C_KET"):
            self.match("IDENTIFIER")
            comp = r_typ.components.lookup(self.mh,
                                           self.ct,
                                           ast.Record_Component)
            self.match("ASSIGN")
            value = self.parse_value(comp.typ)
            obj.assign(comp, value)

        # Check that each non-optional component has been specified
        for comp in r_typ.all_components():
            if obj.field[comp.name] is None:
                if not comp.optional:
                    self.mh.error(
                        obj.location,
                        "required component %s (see %s) is not defined" %
                        (comp.name,
                         comp.location.to_string(False)))
                else:
                    obj.assign(comp, ast.Implicit_Null(obj, comp))

        self.match("C_KET")

    def parse_trlc_entry(self):
        if self.peek_kw("section"):
            self.parse_section_declaration()
        else:
            self.parse_record_object_declaration()

    def parse_rsl_header(self):
        self.match_kw("package")
        self.match("IDENTIFIER")

        self.pkg = ast.Package(self.ct.value,
                               self.ct.location,
                               self.stab)
        self.stab.register(self.mh, self.pkg)
        self.default_scope.push(self.pkg.symbols)

        while self.peek_kw("import"):
            self.match_kw("import")
            self.match("IDENTIFIER")
            self.raw_deps.append(self.ct)
            self.imports.add(self.ct.value)

    def parse_rsl_file(self):
        assert self.pkg is not None

        while self.peek_kw("enum") or \
              self.peek_kw("type") or \
              self.peek_kw("checks"):
            if self.peek_kw("enum") or self.peek_kw("type"):
                self.parse_type_declaration()
            else:
                self.parse_check_block()

        self.match_eof()

    def parse_check_file(self):
        self.match_kw("package")
        self.match("IDENTIFIER")

        self.pkg = self.stab.lookup(self.mh, self.ct, ast.Package)
        self.default_scope.push(self.pkg.symbols)

        while not self.peek_eof():
            self.parse_check_block()

        self.match_eof()

    def parse_trlc_file(self):
        self.match_kw("package")
        self.match("IDENTIFIER")

        if self.stab.contains(self.ct.value):
            self.pkg = self.stab.lookup(self.mh, self.ct, ast.Package)
        else:
            self.pkg = ast.Package(self.ct.value,
                                   self.ct.location,
                                   self.stab)
            self.pkg.declared_late = True
            self.stab.register(self.mh, self.pkg)
        self.default_scope.push(self.pkg.symbols)

        while self.peek_kw("import"):
            self.match_kw("import")
            self.match("IDENTIFIER")
            pkg = self.stab.lookup(self.mh, self.ct, ast.Package)
            if pkg.declared_late:
                self.mh.error(self.ct.location,
                              "package must be declared in rsl file to be"
                              " importable")
            self.imports.add(pkg.name)

        while self.peek_kw("section") or self.peek("IDENTIFIER"):
            self.parse_trlc_entry()

        self.match_eof()
