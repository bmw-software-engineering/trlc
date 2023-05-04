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

import re

from trlc.nested import Nested_Lexer
from trlc.lexer import Token_Base, Token, Lexer_Base, TRLC_Lexer
from trlc.errors import Message_Handler
from trlc import ast


class Markup_Token(Token_Base):
    KIND = frozenset(["CHARACTER",
                      "REFLIST_BEGIN",
                      "REFLIST_END",
                      "REFLIST_COMMA",
                      "REFLIST_DOT",
                      "REFLIST_IDENTIFIER"])

    def __init__(self, location, kind, value):
        super().__init__(location, kind, value)
        assert isinstance(value, str)


class Markup_Lexer(Nested_Lexer):
    def __init__(self, mh, literal):
        super().__init__(mh, literal)

        self.in_reflist = False

    def file_location(self):
        return self.origin_location

    def token(self):
        if self.in_reflist:
            self.skip_whitespace()
        else:
            self.advance()
        if self.cc is None:
            return None

        start_pos  = self.lexpos
        start_line = self.line_no
        start_col  = self.col_no

        if self.cc == "[" and self.nc == "[":
            kind = "REFLIST_BEGIN"
            self.advance()
            if self.in_reflist:
                self.mh.lex_error(self.source_location(start_line,
                                                       start_col,
                                                       start_pos,
                                                       start_pos + 1),
                                  "cannot nest reference lists")
            else:
                self.in_reflist = True

        elif self.cc == "]" and self.nc == "]":
            kind = "REFLIST_END"
            self.advance()
            if self.in_reflist:
                self.in_reflist = False
            else:
                self.mh.lex_error(self.source_location(start_line,
                                                       start_col,
                                                       start_pos,
                                                       start_pos + 1),
                                  "opening [[ for this ]] found")

        elif not self.in_reflist:
            kind = "CHARACTER"

        elif self.cc == ",":
            kind = "REFLIST_COMMA"

        elif self.cc == ".":
            kind = "REFLIST_DOT"

        elif self.is_alpha(self.cc):
            kind = "REFLIST_IDENTIFIER"
            while self.nc and (self.is_alnum(self.nc) or
                               self.nc == "_"):
                self.advance()

        else:
            self.mh.lex_error(self.source_location(start_line,
                                                   start_col,
                                                   start_pos,
                                                   start_pos),
                              "unexpected character '%s'" % self.cc)

        loc = self.source_location(start_line,
                                   start_col,
                                   start_pos,
                                   self.lexpos)

        return Markup_Token(loc,
                            kind,
                            self.content[start_pos:self.lexpos + 1])


class Parser_Base:
    def __init__(self, mh, lexer, eoc_name, token_kinds, keywords):
        assert isinstance(mh, Message_Handler)
        assert isinstance(lexer, Lexer_Base)
        assert isinstance(eoc_name, str)
        assert isinstance(token_kinds, frozenset)
        assert isinstance(keywords, frozenset)
        self.mh    = mh
        self.lexer = lexer

        self.eoc_name          = eoc_name
        self.language_tokens   = token_kinds
        self.language_keywords = keywords

        self.ct = None
        self.nt = None
        self.advance()

    def advance(self):
        self.ct = self.nt
        while True:
            self.nt = self.lexer.token()
            if self.nt is None or self.nt.kind != "COMMENT":
                break

    def peek(self, kind):
        assert kind in self.language_tokens
        return self.nt is not None and self.nt.kind == kind

    def peek_eof(self):
        return self.nt is None

    def peek_kw(self, value):
        assert value in self.language_keywords
        return self.peek("KEYWORD") and self.nt.value == value

    def match(self, kind):
        assert kind in self.language_tokens
        if self.nt is None:
            if self.ct is None:
                self.mh.error(self.lexer.file_location(),
                              "expected %s, encountered %s instead" %
                              (kind, self.eoc_name))
            else:
                self.mh.error(self.ct.location,
                              "expected %s, encountered %s instead" %
                              (kind, self.eoc_name))
        elif self.nt.kind != kind:
            self.mh.error(self.nt.location,
                          "expected %s, encountered %s instead" %
                          (kind, self.nt.kind))
        self.advance()

    def match_eof(self):
        if self.nt is not None:
            self.mh.error(self.nt.location,
                          "expected %s, encountered %s instead" %
                          (self.eoc_name, self.nt.kind))

    def match_kw(self, value):
        assert value in self.language_keywords
        if self.nt is None:
            if self.ct is None:
                self.mh.error(self.lexer.file_location(),
                              "expected %s, encountered %s instead" %
                              (value, self.eoc_name))
            else:
                self.mh.error(self.ct.location,
                              "expected %s, encountered %s instead" %
                              (value, self.eoc_name))
        elif self.nt.kind != "KEYWORD":
            self.mh.error(self.nt.location,
                          "expected %s, encountered %s instead" %
                          (value, self.nt.kind))
        elif self.nt.value != value:
            self.mh.error(self.nt.location,
                          "expected %s, encountered %s instead" %
                          (value, self.nt.value))
        self.advance()


class Markup_Parser(Parser_Base):
    def __init__(self, parent, literal):
        assert isinstance(parent, Parser)
        super().__init__(parent.mh, Markup_Lexer(parent.mh, literal),
                         eoc_name    = "end-of-string",
                         token_kinds = Markup_Token.KIND,
                         keywords    = frozenset())
        self.parent     = parent
        self.references = literal.references

    def parse_all_references(self):
        while self.nt:
            if self.peek("CHARACTER"):
                self.advance()
            else:
                self.parse_ref_list()
        self.match_eof()
        return self.references

    def parse_ref_list(self):
        self.match("REFLIST_BEGIN")
        self.parse_qualified_name()
        while self.peek("REFLIST_COMMA"):
            self.match("REFLIST_COMMA")
            self.parse_qualified_name()
        self.match("REFLIST_END")

    def parse_qualified_name(self):
        self.match("REFLIST_IDENTIFIER")
        if self.peek("REFLIST_DOT"):
            package = self.parent.stab.lookup_direct(
                mh                = self.mh,
                name              = self.ct.value,
                error_location    = self.ct.location,
                required_subclass = ast.Package)
            if package != self.parent.pkg and \
               package.name not in self.parent.imports:
                self.mh.error(self.ct.location,
                              "package must be imported before use")

            self.match("REFLIST_DOT")
            self.match("REFLIST_IDENTIFIER")
        else:
            package = self.parent.pkg

        ref = ast.Record_Reference(location = self.ct.location,
                                   name     = self.ct.value,
                                   typ      = None,
                                   package  = package)
        self.references.append(ref)


class Parser(Parser_Base):
    COMPARISON_OPERATOR = ("==", "!=", "<", "<=", ">", ">=")
    ADDING_OPERATOR = ("+", "-")
    MULTIPLYING_OPERATOR = ("*", "/", "%")

    def __init__(self, mh, stab, file_name, lint_mode, lexer=None):
        assert isinstance(mh, Message_Handler)
        assert isinstance(stab, ast.Symbol_Table)
        assert isinstance(file_name, str)
        assert isinstance(lint_mode, bool)
        if lexer:
            super().__init__(mh, lexer,
                             eoc_name    = "end-of-file",
                             token_kinds = Token.KIND,
                             keywords    = TRLC_Lexer.KEYWORDS)
        else:
            super().__init__(mh, TRLC_Lexer(mh, file_name),
                             eoc_name    = "end-of-file",
                             token_kinds = Token.KIND,
                             keywords    = TRLC_Lexer.KEYWORDS)
        self.lint_mode = lint_mode
        self.stab      = stab
        self.pkg       = None
        self.raw_deps  = []
        self.deps      = []
        self.imports   = set()

        self.builtin_bool    = stab.table["Boolean"]
        self.builtin_int     = stab.table["Integer"]
        self.builtin_decimal = stab.table["Decimal"]
        self.builtin_str     = stab.table["String"]
        self.builtin_mstr    = stab.table["Markup_String"]

        self.section = []
        self.default_scope = ast.Scope()
        self.default_scope.push(self.stab)

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
        assert required_subclass is None or isinstance(required_subclass, type)
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
        elif self.peek_kw("tuple"):
            self.parse_tuple_declaration()
        else:
            self.parse_record_declaration()

    def parse_enum_declaration(self):
        self.match_kw("enum")
        name, description = self.parse_described_name()

        enum = ast.Enumeration_Type(name        = name.value,
                                    description = description,
                                    location    = name.location,
                                    package     = self.pkg)
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

    def parse_tuple_field(self,
                          n_tuple,
                          optional_allowed,
                          optional_reason,
                          optional_required):
        assert isinstance(n_tuple, ast.Tuple_Type)
        assert isinstance(optional_allowed, bool)
        assert isinstance(optional_reason, str)
        assert isinstance(optional_required, bool)
        assert optional_allowed or not optional_required

        field_name, field_description = self.parse_described_name()

        if optional_required or self.peek_kw("optional"):
            self.match_kw("optional")
            if optional_allowed:
                field_is_optional = True
            else:
                self.mh.error(self.ct.location, optional_reason)
        else:
            field_is_optional = False

        field_type = self.parse_qualified_name(self.default_scope,
                                               ast.Type)

        return ast.Composite_Component(
            name        = field_name.value,
            description = field_description,
            location    = field_name.location,
            member_of   = n_tuple,
            n_typ       = field_type,
            optional    = field_is_optional)

    def parse_tuple_declaration(self):
        self.match_kw("tuple")
        name, description = self.parse_described_name()

        n_tuple = ast.Tuple_Type(name        = name.value,
                                 description = description,
                                 location    = name.location,
                                 package     = self.pkg)

        self.match("C_BRA")

        n_field = self.parse_tuple_field(
            n_tuple,
            optional_allowed  = False,
            optional_reason   = "first field may not be optional",
            optional_required = False)
        n_tuple.components.register(self.mh, n_field)

        has_separators    = False
        optional_required = False
        separator_allowed = True

        while self.peek_kw("separator") or self.peek("IDENTIFIER"):
            if has_separators or self.peek_kw("separator"):
                has_separators = True
                self.match_kw("separator")
                if not separator_allowed:
                    self.mh.error(self.ct.location,
                                  "either all fields must be separated,"
                                  " or none")
                if self.peek("IDENTIFIER") or \
                   self.peek("AT") or \
                   self.peek("COLON") or \
                   self.peek("SEMICOLON"):
                    self.advance()
                    n_tuple.add_separator(ast.Separator(self.ct))
            else:
                separator_allowed = False
            n_field = self.parse_tuple_field(
                n_tuple,
                optional_allowed  = has_separators,
                optional_reason   = ("optional only permitted in tuples"
                                     " with separators"),
                optional_required = optional_required)
            n_tuple.components.register(self.mh, n_field)
            optional_required |= n_field.optional

        self.match("C_KET")

        # Late registration to avoid recursion in tuples
        self.pkg.symbols.register(self.mh, n_tuple)

    def parse_record_component(self, n_record):
        assert isinstance(n_record, ast.Record_Type)

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

        return ast.Composite_Component(name        = c_name.value,
                                       description = c_descr,
                                       location    = c_name.location,
                                       member_of   = n_record,
                                       n_typ       = c_typ,
                                       optional    = c_optional)

    def parse_record_declaration(self):
        if self.peek_kw("abstract"):
            self.match_kw("abstract")
            is_abstract = True
            is_final    = False
        elif self.peek_kw("final"):
            self.match_kw("final")
            is_abstract = False
            is_final    = True
        else:
            is_abstract = False
            is_final    = False

        self.match_kw("type")
        name, description = self.parse_described_name()

        if self.peek_kw("extends"):
            self.match_kw("extends")
            root_record = self.parse_qualified_name(self.default_scope,
                                                    ast.Record_Type)
        else:
            root_record = None

        if self.lint_mode and \
           root_record and root_record.is_final and \
           not is_final:
            self.mh.warning(name.location,
                            "consider clarifying that this record is final")

        record = ast.Record_Type(name        = name.value,
                                 description = description,
                                 location    = name.location,
                                 package     = self.pkg,
                                 n_parent    = root_record,
                                 is_abstract = is_abstract)
        self.pkg.symbols.register(self.mh, record)

        self.match("C_BRA")
        while not self.peek("C_KET"):
            if self.peek_kw("freeze"):
                self.match_kw("freeze")
                self.match("IDENTIFIER")
                n_comp = record.components.lookup(self.mh,
                                                  self.ct,
                                                  ast.Composite_Component)
                if record.is_frozen(n_comp):
                    n_value = record.get_freezing_expression(n_comp)
                    self.mh.error(
                        self.ct.location,
                        "duplicate freezing of %s, previously frozen at %s" %
                        (n_comp.name,
                         self.mh.cross_file_reference(n_value.location)))
                self.match("ASSIGN")
                n_value = self.parse_value(n_comp.n_typ)

                record.frozen[n_comp.name] = n_value

            else:
                n_comp = self.parse_record_component(record)
                if record.is_final:
                    self.mh.error(n_comp.location,
                                  "cannot declare new components in"
                                  " final record type")
                else:
                    record.components.register(self.mh, n_comp)

        self.match("C_KET")

        # Finally mark record final if applicable
        if is_final:
            record.is_final = True

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

            elif isinstance(n_a.typ, ast.Builtin_String):
                rv = ast.Binary_Expression(
                    mh       = self.mh,
                    location = t_in.location,
                    typ      = self.builtin_bool,
                    operator = ast.Binary_Operator.STRING_CONTAINS,
                    n_lhs    = n_lhs,
                    n_rhs    = n_a)

            elif isinstance(n_a.typ, ast.Array_Type):
                rv = ast.Binary_Expression(
                    mh       = self.mh,
                    location = t_in.location,
                    typ      = self.builtin_bool,
                    operator = ast.Binary_Operator.ARRAY_CONTAINS,
                    n_lhs    = n_lhs,
                    n_rhs    = n_a)

            else:
                self.mh.error(
                    n_a.location,
                    "membership test only defined for Strings and Arrays,"
                    " not for %s" % n_a.typ.name)

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

        if isinstance(n_lhs.typ, ast.Builtin_String):
            rtyp = self.builtin_str
        else:
            rtyp = n_lhs.typ

        while self.peek("OPERATOR") and \
              self.nt.value in Parser.ADDING_OPERATOR:
            self.match("OPERATOR")
            t_op  = self.ct
            n_rhs = self.parse_term(scope)
            n_lhs = ast.Binary_Expression(
                mh       = self.mh,
                location = t_op.location,
                typ      = rtyp,
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
                typ       = n_operand.typ,
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
                    typ      = n_lhs.typ,
                    operator = ast.Binary_Operator.POWER,
                    n_lhs    = n_lhs,
                    n_rhs    = n_rhs)
            return n_lhs

    def parse_primary(self, scope):
        assert isinstance(scope, ast.Scope)

        if self.peek("INTEGER"):
            self.match("INTEGER")
            return ast.Integer_Literal(self.ct, self.builtin_int)

        elif self.peek("DECIMAL"):
            self.match("DECIMAL")
            return ast.Decimal_Literal(self.ct, self.builtin_decimal)

        elif self.peek("STRING"):
            self.match("STRING")
            return ast.String_Literal(self.ct, self.builtin_str)

        elif self.peek_kw("true") or self.peek_kw("false"):
            self.match("KEYWORD")
            return ast.Boolean_Literal(self.ct, self.builtin_bool)

        elif self.peek_kw("null"):
            self.match_kw("null")
            return ast.Null_Literal(self.ct)

        elif self.peek("BRA"):
            self.match("BRA")
            if self.peek_kw("forall") or self.peek_kw("exists"):
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

        if self.peek_kw("forall"):
            self.match_kw("forall")
            universal = True
        else:
            self.match_kw("exists")
            universal = False
        loc = self.ct.location
        self.match("IDENTIFIER")
        t_qv = self.ct
        if scope.contains(t_qv.value):
            pdef = scope.lookup(self.mh, t_qv)
            self.mh.error(t_qv.location,
                          "shadows %s %s from %s" %
                          (pdef.__class__.__name__,
                           pdef.name,
                           self.mh.cross_file_reference(pdef.location)))
        self.match_kw("in")
        self.match("IDENTIFIER")
        field = scope.lookup(self.mh, self.ct, ast.Composite_Component)
        n_source = ast.Name_Reference(self.ct.location,
                                      field)
        if not isinstance(field.n_typ, ast.Array_Type):
            self.mh.error(self.ct.location,
                          "you can only quantify over arrays")
        n_var = ast.Quantified_Variable(t_qv.value,
                                        t_qv.location,
                                        field.n_typ.element_type)
        self.match("ARROW")

        new_table = ast.Symbol_Table()
        new_table.register(self.mh, n_var)
        scope.push(new_table)
        n_expr = self.parse_expression(scope)
        scope.pop()

        return ast.Quantified_Expression(mh         = self.mh,
                                         location   = loc,
                                         typ        = self.builtin_bool,
                                         universal  = universal,
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
        assert isinstance(n_name, (ast.Builtin_Function,
                                   ast.Builtin_Numeric_Type))
        assert isinstance(t_name, Token)

        # Lint: complain about old functions
        if isinstance(n_name, ast.Builtin_Function) and \
           self.lint_mode and n_name.deprecated:
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
        if isinstance(n_name, ast.Builtin_Function):
            required_arity = n_name.arity
        else:
            required_arity = 1
        if required_arity != len(parameters):
            self.mh.error(t_name.location,
                          "function requires %u parameters" %
                          n_name.arity)

        # Enforce types
        if n_name.name in ("len", "trlc:len"):
            if isinstance(parameters[0].typ, ast.Builtin_String):
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
                # scope is None on purpose to enforce static context
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

        elif isinstance(n_name, ast.Builtin_Numeric_Type):
            parameters[0].ensure_type(self.mh, ast.Builtin_Numeric_Type)
            if isinstance(n_name, ast.Builtin_Integer):
                return ast.Unary_Expression(
                    mh        = self.mh,
                    location  = t_name.location,
                    typ       = self.builtin_int,
                    operator  = ast.Unary_Operator.CONVERSION_TO_INT,
                    n_operand = parameters[0])
            elif isinstance(n_name, ast.Builtin_Decimal):
                return ast.Unary_Expression(
                    mh        = self.mh,
                    location  = t_name.location,
                    typ       = self.builtin_decimal,
                    operator  = ast.Unary_Operator.CONVERSION_TO_DECIMAL,
                    n_operand = parameters[0])
            else:
                self.mh.ice_loc(t_name.location,
                                "unexpected type conversion")

        else:
            self.mh.ice_loc(t_name.location,
                            "unexpected builtin")

    def parse_name(self, scope):
        # This is a bit more complex. The grammar is:
        #
        # qualified_name ::= [ IDENTIFIER_package_name '.' ] IDENTIFIER_name
        #
        # name ::= qualified_name
        #        | BUILTIN_IDENTIFIER
        #        | name '.' IDENTIFIER
        #        | name '[' expression ']'
        #        | name '(' parameter_list ')'
        #
        # parameter_list ::= expression { ',' expression }

        assert isinstance(scope, ast.Scope)

        # All names start with a (qualified) identifier. We parse that
        # first. There is a special complication for functions, as
        # builtin functions (e.g. len) can shadow record
        # components. However as functions cannot be stored in
        # components the true grammar for function calls is always
        # IDENTIFIER '('; so we can slightly special case this.

        if self.peek("BUILTIN"):
            # Legacy builtin function call. The lookup in the root
            # scope is not an error.
            self.match("BUILTIN")
            n_name = self.stab.lookup(self.mh, self.ct, ast.Builtin_Function)

        else:
            self.match("IDENTIFIER")
            if self.peek("BRA"):
                # There is one more way we can have a builtin
                # function, if we follow our name with brackets
                # immediately.
                n_name = self.stab.lookup(self.mh,
                                          self.ct)
                if not isinstance(n_name, (ast.Builtin_Function,
                                           ast.Builtin_Numeric_Type)):
                    self.mh.error(self.ct.location,
                                  "not a valid builtin function "
                                  "or numeric type")
            else:
                n_name = self.parse_qualified_name(scope, match_ident=False)

        # Enum literals are a bit different, so we deal with themq
        # first.
        if isinstance(n_name, ast.Enumeration_Type):
            self.match("DOT")
            self.match("IDENTIFIER")
            lit = n_name.literals.lookup(self.mh,
                                         self.ct,
                                         ast.Enumeration_Literal_Spec)
            return ast.Enumeration_Literal(location = self.ct.location,
                                           literal  = lit)

        # Anything that remains is either a function call or an actual
        # name. Let's just enforce this for sanity.
        if not isinstance(n_name, (ast.Builtin_Function,
                                   ast.Builtin_Numeric_Type,
                                   ast.Composite_Component,
                                   ast.Quantified_Variable,
                                   )):
            self.mh.error(self.ct.location,
                          "%s %s is not a valid name" %
                          (n_name.__class__.__name__,
                           n_name.name))

        # Right now function calls and type conversions must be
        # top-level, so let's get these out of the way as well.
        if isinstance(n_name, (ast.Builtin_Function,
                               ast.Builtin_Numeric_Type)):
            return self.parse_builtin(scope, n_name, self.ct)

        assert isinstance(n_name, (ast.Composite_Component,
                                   ast.Quantified_Variable))

        # We now process the potentially recursive part:
        #        | name '.' IDENTIFIER
        #        | name '[' expression ']'
        n_name = ast.Name_Reference(location = self.ct.location,
                                    entity   = n_name)

        while self.peek("DOT") or self.peek("S_BRA"):
            if self.peek("DOT"):
                if not isinstance(n_name.typ, ast.Tuple_Type):
                    self.mh.error(n_name.location,
                                  "expression '%s' has type %s, "
                                  "which is not a tuple" %
                                  (n_name.to_string(),
                                   n_name.typ.name))
                self.match("DOT")
                self.match("IDENTIFIER")
                n_field = n_name.typ.components.lookup(self.mh,
                                                       self.ct,
                                                       ast.Composite_Component)
                n_name = ast.Field_Access_Expression(
                    mh       = self.mh,
                    location = self.ct.location,
                    n_prefix = n_name,
                    n_field  = n_field)

            elif self.peek("S_BRA"):
                if not isinstance(n_name.typ, ast.Array_Type):
                    self.mh.error(n_name.location,
                                  "expression '%s' has type %s, "
                                  "which is not an array" %
                                  (n_name.to_string(),
                                   n_name.typ.name))

                self.match("S_BRA")
                t_bracket = self.ct
                n_index = self.parse_expression(scope)
                self.match("S_KET")

                n_name = ast.Binary_Expression(
                    mh       = self.mh,
                    location = t_bracket.location,
                    typ      = n_name.typ.element_type,
                    operator = ast.Binary_Operator.INDEX,
                    n_lhs    = n_name,
                    n_rhs    = n_index)

        return n_name

    def parse_check_block(self):
        self.match_kw("checks")
        self.match("IDENTIFIER")
        n_ctype = self.pkg.symbols.lookup(self.mh, self.ct, ast.Composite_Type)
        scope = ast.Scope()
        scope.push(self.stab)
        scope.push(self.pkg.symbols)
        scope.push(n_ctype.components)
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
                c_anchor = n_ctype.components.lookup(self.mh,
                                                     self.ct,
                                                     ast.Composite_Component)
            else:
                c_anchor = None

            n_check = ast.Check(n_type    = n_ctype,
                                n_expr    = c_expr,
                                n_anchor  = c_anchor,
                                severity  = c_sev,
                                t_message = t_msg)
            n_ctype.add_check(n_check)

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

        if isinstance(typ, ast.Builtin_Numeric_Type):
            if self.peek("OPERATOR") and \
               self.nt.value in Parser.ADDING_OPERATOR:
                self.match("OPERATOR")
                t_op = self.ct
                e_op = (ast.Unary_Operator.PLUS
                        if t_op.value == "+"
                        else ast.Unary_Operator.MINUS)
            else:
                t_op = None

            if self.peek("DECIMAL"):
                self.match("DECIMAL")
                rv = ast.Decimal_Literal(self.ct, self.builtin_decimal)

            else:
                self.match("INTEGER")
                rv = ast.Integer_Literal(self.ct, self.builtin_int)

            if t_op:
                rv = ast.Unary_Expression(mh        = self.mh,
                                          location  = t_op.location,
                                          typ       = rv.typ,
                                          operator  = e_op,
                                          n_operand = rv)

            return rv

        elif isinstance(typ, ast.Builtin_Markup_String):
            return self.parse_markup_string()

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

            if len(rv.value) < typ.lower_bound:
                self.mh.error(self.ct.location,
                              "this array requires at least %u elements "
                              "(only %u provided)" %
                              (typ.lower_bound,
                               len(rv.value)),
                              fatal=False)
            if typ.upper_bound and len(rv.value) > typ.upper_bound:
                self.mh.error(rv.value[typ.upper_bound].location,
                              "this array requires at most %u elements "
                              "(%u provided)" %
                              (typ.upper_bound,
                               len(rv.value)),
                              fatal=False)

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

            rv = ast.Record_Reference(location = t_name.location,
                                      name     = t_name.value,
                                      typ      = typ,
                                      package  = the_pkg)
            if the_pkg.symbols.contains(t_name.value):
                rv.target = the_pkg.symbols.lookup(self.mh,
                                                   t_name,
                                                   ast.Record_Object)
                if not rv.target.n_typ.is_subclass_of(typ):
                    self.mh.error(t_name.location,
                                  "incorrect type, expected %s but %s is %s" %
                                  (typ.name,
                                   rv.name,
                                   rv.target.n_typ.name))

            return rv

        elif isinstance(typ, ast.Tuple_Type) and typ.has_separators():
            rv = ast.Tuple_Aggregate(self.nt.location, typ)

            next_is_optional = False
            for n_item in typ.iter_sequence():
                if isinstance(n_item, ast.Composite_Component):
                    if next_is_optional and n_item.optional:
                        break
                    rv.assign(n_item.name,
                              self.parse_value(n_item.n_typ))

                elif n_item.token.kind in ("AT", "COLON", "SEMICOLON"):
                    if self.peek(n_item.token.kind):
                        self.match(n_item.token.kind)
                    else:
                        next_is_optional = True

                elif n_item.token.kind == "IDENTIFIER":
                    if self.peek("IDENTIFIER") and \
                       self.nt.value == n_item.token.value:
                        self.match("IDENTIFIER")
                    else:
                        next_is_optional = True

                else:
                    assert False

            return rv

        elif isinstance(typ, ast.Tuple_Type) and not typ.has_separators():
            self.match("BRA")
            rv = ast.Tuple_Aggregate(self.ct.location, typ)

            first = True
            for n_field in typ.iter_sequence():
                if first:
                    first = False
                else:
                    self.match("COMMA")
                rv.assign(n_field.name,
                          self.parse_value(n_field.n_typ))

            self.match("KET")
            return rv

        else:
            self.mh.ice_loc(self.ct.location,
                            "logic error: unexpected type %s" %
                            typ.__class__.__name__)

    def parse_markup_string(self):
        self.match("STRING")
        rv = ast.String_Literal(self.ct, self.builtin_mstr)
        mpar = Markup_Parser(self, rv)
        mpar.parse_all_references()
        return rv

    def parse_record_object_declaration(self):
        r_typ = self.parse_qualified_name(self.default_scope,
                                          ast.Record_Type)
        if r_typ.is_abstract:
            self.mh.error(self.ct.location,
                          "cannot declare object of abstract record type %s" %
                          r_typ.name)

        self.match("IDENTIFIER")
        obj = ast.Record_Object(
            name     = self.ct.value,
            location = self.ct.location,
            n_typ    = r_typ,
            section  = self.section[-1] if self.section else None)
        self.pkg.symbols.register(self.mh, obj)
        self.match("C_BRA")
        while not self.peek("C_KET"):
            self.match("IDENTIFIER")
            comp = r_typ.components.lookup(self.mh,
                                           self.ct,
                                           ast.Composite_Component)
            if r_typ.is_frozen(comp):
                self.mh.error(self.ct.location,
                              "cannot overwrite frozen component %s" %
                              comp.name)
            self.match("ASSIGN")
            value = self.parse_value(comp.n_typ)
            obj.assign(comp, value)

        # Check that each non-optional component has been specified
        for comp in r_typ.all_components():
            if obj.field[comp.name] is None:
                if r_typ.is_frozen(comp):
                    obj.assign(comp, r_typ.get_freezing_expression(comp))
                elif not comp.optional:
                    self.mh.error(
                        obj.location,
                        "required component %s (see %s) is not defined" %
                        (comp.name,
                         self.mh.cross_file_reference(comp.location)))
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

        while not self.peek_eof():
            if self.peek_kw("checks"):
                self.parse_check_block()
            else:
                self.parse_type_declaration()

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
