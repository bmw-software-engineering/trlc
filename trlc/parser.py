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
from trlc.errors import Message_Handler, TRLC_Error
from trlc import ast


class Markup_Token(Token_Base):
    # lobster-trace: LRM.Markup_String_Format

    KIND = {
        "CHARACTER"          : "character",
        "REFLIST_BEGIN"      : "[[",
        "REFLIST_END"        : "]]",
        "REFLIST_COMMA"      : ",",
        "REFLIST_DOT"        : ".",
        "REFLIST_IDENTIFIER" : "identifier",
    }

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
        # lobster-trace: LRM.Markup_String_Errors

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

        # pylint: disable=possibly-used-before-assignment
        return Markup_Token(loc,
                            kind,
                            self.content[start_pos:self.lexpos + 1])


class Parser_Base:
    def __init__(self, mh, lexer, eoc_name, token_map, keywords):
        assert isinstance(mh, Message_Handler)
        assert isinstance(lexer, Lexer_Base)
        assert isinstance(eoc_name, str)
        assert isinstance(token_map, dict)
        assert isinstance(keywords, frozenset)
        self.mh    = mh
        self.lexer = lexer

        self.eoc_name          = eoc_name
        self.language_tokens   = token_map
        self.language_keywords = keywords

        self.ct = None
        self.nt = None
        self.advance()

    def advance(self):
        # lobster-trace: LRM.Comments
        self.ct = self.nt
        while True:
            self.nt = self.lexer.token()
            if self.nt is None or self.nt.kind != "COMMENT":
                break

    def skip_until_newline(self):
        if self.ct is None:
            return
        current_line = self.ct.location.line_no
        while self.nt and self.nt.location.line_no == current_line:
            self.advance()

    def peek(self, kind):
        assert kind in self.language_tokens, \
            "%s is not a valid token" % kind
        return self.nt is not None and self.nt.kind == kind

    def peek_eof(self):
        return self.nt is None

    def peek_kw(self, value):
        assert value in self.language_keywords, \
            "%s is not a valid keyword" % value
        return self.peek("KEYWORD") and self.nt.value == value

    def match(self, kind):
        # lobster-trace: LRM.Matching_Value_Types

        assert kind in self.language_tokens, \
            "%s is not a valid token" % kind
        if self.nt is None:
            if self.ct is None:
                self.mh.error(self.lexer.file_location(),
                              "expected %s, encountered %s instead" %
                              (self.language_tokens[kind], self.eoc_name))
            else:
                self.mh.error(self.ct.location,
                              "expected %s, encountered %s instead" %
                              (self.language_tokens[kind], self.eoc_name))
        elif self.nt.kind != kind:
            self.mh.error(self.nt.location,
                          "expected %s, encountered %s instead" %
                          (self.language_tokens[kind],
                           self.language_tokens[self.nt.kind]))
        self.advance()

    def match_eof(self):
        if self.nt is not None:
            self.mh.error(self.nt.location,
                          "expected %s, encountered %s instead" %
                          (self.eoc_name,
                           self.language_tokens[self.nt.kind]))

    def match_kw(self, value):
        assert value in self.language_keywords, \
            "%s is not a valid keyword" % value
        if self.nt is None:
            if self.ct is None:
                self.mh.error(self.lexer.file_location(),
                              "expected keyword %s, encountered %s instead" %
                              (value, self.eoc_name))
            else:
                self.mh.error(self.ct.location,
                              "expected keyword %s, encountered %s instead" %
                              (value, self.eoc_name))
        elif self.nt.kind != "KEYWORD":
            self.mh.error(self.nt.location,
                          "expected keyword %s, encountered %s instead" %
                          (value,
                           self.language_tokens[self.nt.kind]))
        elif self.nt.value != value:
            self.mh.error(self.nt.location,
                          "expected keyword %s,"
                          " encountered keyword %s instead" %
                          (value, self.nt.value))
        self.advance()


class Markup_Parser(Parser_Base):
    def __init__(self, parent, literal):
        assert isinstance(parent, Parser)
        super().__init__(parent.mh, Markup_Lexer(parent.mh, literal),
                         eoc_name  = "end-of-string",
                         token_map = Markup_Token.KIND,
                         keywords  = frozenset())
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
        # lobster-trace: LRM.Qualified_Name
        # lobster-trace: LRM.Valid_Qualifier
        # lobster-trace: LRM.Valid_Name
        # lobster-trace: LRM.Markup_String_Resolution
        # lobster-trace: LRM.Markup_String_Types

        self.match("REFLIST_IDENTIFIER")
        if self.peek("REFLIST_DOT"):
            package = self.parent.stab.lookup_direct(
                mh                = self.mh,
                name              = self.ct.value,
                error_location    = self.ct.location,
                required_subclass = ast.Package)
            if not self.parent.cu.is_visible(package):
                self.mh.error(self.ct.location,
                              "package must be imported before use")

            self.match("REFLIST_DOT")
            self.match("REFLIST_IDENTIFIER")
        else:
            package = self.parent.cu.package

        ref = ast.Record_Reference(location = self.ct.location,
                                   name     = self.ct.value,
                                   typ      = None,
                                   package  = package)
        self.references.append(ref)


class Parser(Parser_Base):
    COMPARISON_OPERATOR = ("==", "!=", "<", "<=", ">", ">=")
    ADDING_OPERATOR = ("+", "-")
    MULTIPLYING_OPERATOR = ("*", "/", "%")

    def __init__(self,
                 mh,
                 stab,
                 file_name,
                 lint_mode,
                 error_recovery,
                 primary_file=True,
                 lexer=None):
        assert isinstance(mh, Message_Handler)
        assert isinstance(stab, ast.Symbol_Table)
        assert isinstance(file_name, str)
        assert isinstance(lint_mode, bool)
        assert isinstance(error_recovery, bool)
        assert isinstance(primary_file, bool)
        assert isinstance(lexer, TRLC_Lexer) or lexer is None
        if lexer:
            super().__init__(mh, lexer,
                             eoc_name  = "end-of-file",
                             token_map = Token.KIND,
                             keywords  = TRLC_Lexer.KEYWORDS)
        else:
            super().__init__(mh, TRLC_Lexer(mh, file_name),
                             eoc_name  = "end-of-file",
                             token_map = Token.KIND,
                             keywords  = TRLC_Lexer.KEYWORDS)

        self.lint_mode      = lint_mode
        self.error_recovery = error_recovery

        self.stab = stab
        self.cu   = ast.Compilation_Unit(file_name)

        self.primary   = primary_file
        self.secondary = False
        # Controls if the file is actually fully parsed: primary means
        # it was selected on the command-line and secondary means it
        # was selected by dependency analysis.

        self.builtin_bool    = stab.lookup_assuming(self.mh, "Boolean")
        self.builtin_int     = stab.lookup_assuming(self.mh, "Integer")
        self.builtin_decimal = stab.lookup_assuming(self.mh, "Decimal")
        self.builtin_str     = stab.lookup_assuming(self.mh, "String")
        self.builtin_mstr    = stab.lookup_assuming(self.mh, "Markup_String")

        self.section = []
        self.default_scope = ast.Scope()
        self.default_scope.push(self.stab)

    def parse_described_name(self):
        # lobster-trace: LRM.Described_Names
        # lobster-trace: LRM.Described_Name_Description
        self.match("IDENTIFIER")
        name = self.ct

        if self.peek("STRING"):
            self.match("STRING")
            t_descr = self.ct
            return name, t_descr.value, t_descr
        else:
            return name, None, None

    def parse_qualified_name(self,
                             scope,
                             required_subclass=None,
                             match_ident=True):
        # lobster-trace: LRM.Qualified_Name
        # lobster-trace: LRM.Valid_Qualifier
        # lobster-trace: LRM.Valid_Name
        assert isinstance(scope, ast.Scope)
        assert required_subclass is None or isinstance(required_subclass, type)
        assert isinstance(match_ident, bool)

        if match_ident:
            self.match("IDENTIFIER")
        sym = scope.lookup(self.mh, self.ct)
        sym.set_ast_link(self.ct)

        if isinstance(sym, ast.Package):
            if not self.cu.is_visible(sym):
                self.mh.error(self.ct.location,
                              "package must be imported before use")
            self.match("DOT")
            sym.set_ast_link(self.ct)
            self.match("IDENTIFIER")
            return sym.symbols.lookup(self.mh, self.ct, required_subclass)
        else:
            # Easiest way to generate the correct error message
            return scope.lookup(self.mh, self.ct, required_subclass)

    def parse_type_declaration(self):
        # lobster-trace: LRM.Type_Declarations
        if self.peek_kw("enum"):
            n_item = self.parse_enum_declaration()
        elif self.peek_kw("tuple"):
            n_item = self.parse_tuple_declaration()
        else:
            n_item = self.parse_record_declaration()
        assert isinstance(n_item, ast.Concrete_Type)
        return n_item

    def parse_enum_declaration(self):
        # lobster-trace: LRM.Enumeration_Declaration
        self.match_kw("enum")
        t_enum = self.ct
        name, description, t_description = self.parse_described_name()

        enum = ast.Enumeration_Type(name        = name.value,
                                    description = description,
                                    location    = name.location,
                                    package     = self.cu.package)
        self.cu.package.symbols.register(self.mh, enum)
        enum.set_ast_link(t_enum)
        enum.set_ast_link(name)
        if t_description:
            enum.set_ast_link(t_description)

        self.match("C_BRA")
        enum.set_ast_link(self.ct)
        empty = True
        while not self.peek("C_KET"):
            name, description, t_description = self.parse_described_name()
            lit = ast.Enumeration_Literal_Spec(name        = name.value,
                                               description = description,
                                               location    = name.location,
                                               enum        = enum)
            lit.set_ast_link(name)
            if t_description:
                lit.set_ast_link(self.ct)
            empty = False
            enum.literals.register(self.mh, lit)
        self.match("C_KET")
        enum.set_ast_link(self.ct)

        if empty:
            # lobster-trace: LRM.No_Empty_Enumerations
            self.mh.error(enum.location,
                          "empty enumerations are not permitted")

        return enum

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

        field_name, field_description, t_descr = self.parse_described_name()

        if optional_required or self.peek_kw("optional"):
            self.match_kw("optional")
            t_optional        = self.ct
            field_is_optional = True
            if not optional_allowed:
                self.mh.error(self.ct.location, optional_reason)
        else:
            field_is_optional = False
            t_optional        = None

        # lobster-trace: LRM.Tuple_Field_Types
        field_type = self.parse_qualified_name(self.default_scope,
                                               ast.Type)
        comp = ast.Composite_Component(name        = field_name.value,
                                       description = field_description,
                                       location    = field_name.location,
                                       member_of   = n_tuple,
                                       n_typ       = field_type,
                                       optional    = field_is_optional)
        comp.set_ast_link(field_name)
        if t_descr:
            comp.set_ast_link(t_descr)
        if field_is_optional:
            comp.set_ast_link(t_optional)

        return comp

    def parse_tuple_declaration(self):
        # lobster-trace: LRM.Tuple_Declaration
        self.match_kw("tuple")
        t_tuple = self.ct
        name, description, t_descr = self.parse_described_name()

        n_tuple = ast.Tuple_Type(name        = name.value,
                                 description = description,
                                 location    = name.location,
                                 package     = self.cu.package)

        n_tuple.set_ast_link(t_tuple)
        n_tuple.set_ast_link(name)
        if t_descr:
            n_tuple.set_ast_link(t_descr)
        self.match("C_BRA")
        n_tuple.set_ast_link(self.ct)

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
                t_sep = self.ct
                if not separator_allowed:
                    # lobster-trace: LRM.Tuple_Separators_All_Or_None
                    self.mh.error(self.ct.location,
                                  "either all fields must be separated,"
                                  " or none")
                if self.peek("IDENTIFIER") or \
                   self.peek("AT") or \
                   self.peek("COLON") or \
                   self.peek("SEMICOLON"):
                    self.advance()
                    sep = ast.Separator(self.ct)
                    sep.set_ast_link(t_sep)
                    sep.set_ast_link(self.ct)
                    n_tuple.add_separator(sep)
            else:
                separator_allowed = False
            # lobster-trace: LRM.Tuple_Optional_Requires_Separators
            n_field = self.parse_tuple_field(
                n_tuple,
                optional_allowed  = has_separators,
                optional_reason   = ("optional only permitted in tuples"
                                     " with separators"),
                optional_required = optional_required)
            n_tuple.components.register(self.mh, n_field)
            # lobster-trace: LRM.Tuple_Optional_Fields
            optional_required |= n_field.optional

        self.match("C_KET")
        n_tuple.set_ast_link(self.ct)

        # Final check to ban tuples with separators containing other
        # tuples.
        if has_separators:
            # lobster-trace: LRM.Restricted_Tuple_Nesting
            for n_field in n_tuple.components.values():
                if isinstance(n_field.n_typ, ast.Tuple_Type) and \
                   n_field.n_typ.has_separators():
                    self.mh.error(
                        n_field.location,
                        "tuple type %s, which contains separators,"
                        " may not contain another tuple with separators"
                        % n_tuple.name)

        # Late registration to avoid recursion in tuples
        # lobster-trace: LRM.Tuple_Field_Types
        self.cu.package.symbols.register(self.mh, n_tuple)

        return n_tuple

    def parse_record_component(self, n_record):
        assert isinstance(n_record, ast.Record_Type)

        c_name, c_descr, t_descr = self.parse_described_name()
        t_optional = None
        c_optional = False
        if self.peek_kw("optional"):
            self.match_kw("optional")
            t_optional = self.ct
            c_optional = True
        c_typ = self.parse_qualified_name(self.default_scope,
                                          ast.Type)
        c_typ.set_ast_link(self.ct)

        if self.peek("S_BRA"):
            self.match("S_BRA")
            t_s_bra = self.ct
            self.match("INTEGER")
            t_lo = self.ct
            a_lo = self.ct.value
            loc_lo = self.ct.location
            self.match("RANGE")
            t_range = self.ct
            a_loc = self.ct.location
            a_hi  = None
            if self.peek("INTEGER"):
                self.match("INTEGER")
                a_hi = self.ct.value
            elif self.peek("OPERATOR") and self.nt.value == "*":
                self.match("OPERATOR")
            else:
                self.mh.error(self.nt.location,
                              "expected INTEGER or * for upper bound")
            t_hi = self.ct
            loc_hi = self.ct.location
            self.match("S_KET")
            t_s_ket = self.ct
            c_typ = ast.Array_Type(location     = a_loc,
                                   element_type = c_typ,
                                   lower_bound  = a_lo,
                                   upper_bound  = a_hi,
                                   loc_lower    = loc_lo,
                                   loc_upper    = loc_hi)
            c_typ.set_ast_link(t_s_bra)
            c_typ.set_ast_link(t_lo)
            c_typ.set_ast_link(t_range)
            c_typ.set_ast_link(t_hi)
            c_typ.set_ast_link(t_s_ket)

        c_comp = ast.Composite_Component(name        = c_name.value,
                                         description = c_descr,
                                         location    = c_name.location,
                                         member_of   = n_record,
                                         n_typ       = c_typ,
                                         optional    = c_optional)
        c_comp.set_ast_link(c_name)
        if t_descr:
            c_comp.set_ast_link(t_descr)
        if c_optional:
            c_comp.set_ast_link(t_optional)

        return c_comp

    def parse_record_declaration(self):
        t_abstract  = None
        t_final     = None
        is_abstract = False
        is_final    = False
        if self.peek_kw("abstract"):
            self.match_kw("abstract")
            t_abstract  = self.ct
            is_abstract = True
        elif self.peek_kw("final"):
            self.match_kw("final")
            t_final  = self.ct
            is_final = True

        self.match_kw("type")
        t_type = self.ct
        name, description, t_description = self.parse_described_name()

        if self.peek_kw("extends"):
            self.match_kw("extends")
            t_extends = self.ct
            root_record = self.parse_qualified_name(self.default_scope,
                                                    ast.Record_Type)
            root_record.set_ast_link(t_extends)
            root_record.set_ast_link(self.ct)
        else:
            root_record = None

        if self.lint_mode and \
           root_record and root_record.is_final and \
           not is_final:
            self.mh.check(name.location,
                          "consider clarifying that this record is final",
                          "clarify_final",
                          ("Parent record %s is final, making this record\n"
                           "also final. Marking it explicitly as final\n"
                           "clarifies this to casual readers." %
                           root_record.fully_qualified_name()))

        record = ast.Record_Type(name        = name.value,
                                 description = description,
                                 location    = name.location,
                                 package     = self.cu.package,
                                 n_parent    = root_record,
                                 is_abstract = is_abstract)
        self.cu.package.symbols.register(self.mh, record)
        if is_abstract:
            record.set_ast_link(t_abstract)
        if is_final:
            record.set_ast_link(t_final)
        record.set_ast_link(t_type)
        record.set_ast_link(name)
        if t_description:
            record.set_ast_link(t_description)

        self.match("C_BRA")
        record.set_ast_link(self.ct)
        while not self.peek("C_KET"):
            if self.peek_kw("freeze"):
                self.match_kw("freeze")
                t_freeze = self.ct
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
                n_comp.set_ast_link(t_freeze)
                n_comp.set_ast_link(self.ct)
                self.match("ASSIGN")
                n_comp.set_ast_link(self.ct)
                n_value = self.parse_value(n_comp.n_typ)
                n_value.set_ast_link(self.ct)

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
        record.set_ast_link(self.ct)

        # Finally mark record final if applicable
        if is_final:
            record.is_final = True

        return record

    def parse_expression(self, scope):
        # lobster-trace: LRM.Expression
        assert isinstance(scope, ast.Scope)

        n_lhs = self.parse_relation(scope)

        if self.peek_kw("and"):
            while self.peek_kw("and"):
                self.match_kw("and")
                t_op  = self.ct
                a_op = ast.Binary_Operator.LOGICAL_AND
                t_op.ast_link = a_op
                n_rhs = self.parse_relation(scope)
                n_lhs = ast.Binary_Expression(
                    mh       = self.mh,
                    location = t_op.location,
                    typ      = self.builtin_bool,
                    operator = a_op,
                    n_lhs    = n_lhs,
                    n_rhs    = n_rhs)

        elif self.peek_kw("or"):
            while self.peek_kw("or"):
                self.match_kw("or")
                t_op  = self.ct
                a_op = ast.Binary_Operator.LOGICAL_OR
                t_op.ast_link = a_op
                n_rhs = self.parse_relation(scope)
                n_lhs = ast.Binary_Expression(
                    mh       = self.mh,
                    location = t_op.location,
                    typ      = self.builtin_bool,
                    operator = a_op,
                    n_lhs    = n_lhs,
                    n_rhs    = n_rhs)

        elif self.peek_kw("xor"):
            self.match_kw("xor")
            t_op  = self.ct
            a_op = ast.Binary_Operator.LOGICAL_XOR
            t_op.ast_link = a_op
            n_rhs = self.parse_relation(scope)
            n_lhs = ast.Binary_Expression(
                mh       = self.mh,
                location = t_op.location,
                typ      = self.builtin_bool,
                operator = a_op,
                n_lhs    = n_lhs,
                n_rhs    = n_rhs)

        elif self.peek_kw("implies"):
            self.match_kw("implies")
            t_op  = self.ct
            a_op = ast.Binary_Operator.LOGICAL_IMPLIES
            t_op.ast_link = a_op
            n_rhs = self.parse_relation(scope)
            n_lhs = ast.Binary_Expression(
                mh       = self.mh,
                location = t_op.location,
                typ      = self.builtin_bool,
                operator = a_op,
                n_lhs    = n_lhs,
                n_rhs    = n_rhs)

        return n_lhs

    def parse_relation(self, scope):
        # lobster-trace: LRM.Relation
        # lobster-trace: LRM.Operators
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
            a_op = relop_mapping[t_op.value]
            t_op.ast_link = a_op
            n_rhs = self.parse_simple_expression(scope)
            return ast.Binary_Expression(
                mh       = self.mh,
                location = t_op.location,
                typ      = self.builtin_bool,
                operator = a_op,
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
            t_n_a = self.ct
            if self.peek("RANGE"):
                self.match("RANGE")
                t_range = self.ct
                n_b = self.parse_simple_expression(scope)
                n_b.set_ast_link(self.ct)
                n_a.set_ast_link(t_n_a)
                rv  = ast.Range_Test(
                    mh       = self.mh,
                    location = t_in.location,
                    typ      = self.builtin_bool,
                    n_lhs    = n_lhs,
                    n_lower  = n_a,
                    n_upper  = n_b)
                rv.set_ast_link(t_range)
                rv.set_ast_link(t_in)

            elif isinstance(n_a.typ, ast.Builtin_String):
                rv = ast.Binary_Expression(
                    mh       = self.mh,
                    location = t_in.location,
                    typ      = self.builtin_bool,
                    operator = ast.Binary_Operator.STRING_CONTAINS,
                    n_lhs    = n_lhs,
                    n_rhs    = n_a)
                rv.set_ast_link(t_in)

            elif isinstance(n_a.typ, ast.Array_Type):
                a_op = ast.Binary_Operator.ARRAY_CONTAINS
                t_in.ast_link = a_op
                rv = ast.Binary_Expression(
                    mh       = self.mh,
                    location = t_in.location,
                    typ      = self.builtin_bool,
                    operator = a_op,
                    n_lhs    = n_lhs,
                    n_rhs    = n_a)

            else:
                self.mh.error(
                    n_a.location,
                    "membership test only defined for Strings and Arrays,"
                    " not for %s" % n_a.typ.name)

            if t_not is not None:
                a_unary_op = ast.Unary_Operator.LOGICAL_NOT
                t_not.ast_link = a_unary_op
                rv = ast.Unary_Expression(
                    mh        = self.mh,
                    location  = t_not.location,
                    typ       = self.builtin_bool,
                    operator  = a_unary_op,
                    n_operand = rv)

            return rv

        else:
            return n_lhs

    def parse_simple_expression(self, scope):
        # lobster-trace: LRM.Simple_Expression
        # lobster-trace: LRM.Operators
        # lobster-trace: LRM.Unary_Minus_Parsing
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
            a_unary = un_add_map[t_unary.value]
            t_unary.ast_link = a_unary
            has_explicit_brackets = self.peek("BRA")
        else:
            t_unary = None

        n_lhs = self.parse_term(scope)
        if t_unary:
            # pylint: disable=possibly-used-before-assignment
            if self.lint_mode and \
               isinstance(n_lhs, ast.Binary_Expression) and \
               not has_explicit_brackets:
                self.mh.check(t_unary.location,
                              "expression means -(%s), place explicit "
                              "brackets to clarify intent" %
                              n_lhs.to_string(),
                              "unary_minus_precedence")

            n_lhs = ast.Unary_Expression(
                mh        = self.mh,
                location  = t_unary.location,
                typ       = n_lhs.typ,
                operator  = a_unary,
                n_operand = n_lhs)

        if isinstance(n_lhs.typ, ast.Builtin_String):
            rtyp = self.builtin_str
        else:
            rtyp = n_lhs.typ

        while self.peek("OPERATOR") and \
              self.nt.value in Parser.ADDING_OPERATOR:
            self.match("OPERATOR")
            t_op  = self.ct
            a_op = bin_add_map[t_op.value]
            t_op.ast_link = a_op
            n_rhs = self.parse_term(scope)
            n_lhs = ast.Binary_Expression(
                mh       = self.mh,
                location = t_op.location,
                typ      = rtyp,
                operator = a_op,
                n_lhs    = n_lhs,
                n_rhs    = n_rhs)

        return n_lhs

    def parse_term(self, scope):
        # lobster-trace: LRM.Term
        # lobster-trace: LRM.Operators
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
            a_op = mul_map[t_op.value]
            t_op.ast_link = a_op
            n_rhs = self.parse_factor(scope)
            n_lhs = ast.Binary_Expression(
                mh       = self.mh,
                location = t_op.location,
                typ      = n_lhs.typ,
                operator = a_op,
                n_lhs    = n_lhs,
                n_rhs    = n_rhs)

        return n_lhs

    def parse_factor(self, scope):
        # lobster-trace: LRM.Factor
        assert isinstance(scope, ast.Scope)

        if self.peek_kw("not"):
            self.match_kw("not")
            t_op      = self.ct
            n_operand = self.parse_primary(scope)
            a_not = ast.Unary_Operator.LOGICAL_NOT
            t_op.ast_link = a_not
            return ast.Unary_Expression(
                mh        = self.mh,
                location  = t_op.location,
                typ       = self.builtin_bool,
                operator  = a_not,
                n_operand = n_operand)

        elif self.peek_kw("abs"):
            self.match_kw("abs")
            t_op      = self.ct
            n_operand = self.parse_primary(scope)
            a_abs = ast.Unary_Operator.ABSOLUTE_VALUE
            t_op.ast_link = a_abs
            return ast.Unary_Expression(
                mh        = self.mh,
                location  = t_op.location,
                typ       = n_operand.typ,
                operator  = a_abs,
                n_operand = n_operand)

        else:
            n_lhs = self.parse_primary(scope)
            if self.peek("OPERATOR") and self.nt.value == "**":
                self.match("OPERATOR")
                t_op  = self.ct
                n_rhs = self.parse_primary(scope)
                rhs_value = n_rhs.evaluate(self.mh, None)
                a_binary = ast.Binary_Operator.POWER
                t_op.ast_link = a_binary
                n_lhs = ast.Binary_Expression(
                    mh       = self.mh,
                    location = t_op.location,
                    typ      = n_lhs.typ,
                    operator = a_binary,
                    n_lhs    = n_lhs,
                    n_rhs    = n_rhs)
                if rhs_value.value < 0:
                    self.mh.error(n_rhs.location,
                                  "exponent must not be negative")
            return n_lhs

    def parse_primary(self, scope):
        # lobster-trace: LRM.Primary
        assert isinstance(scope, ast.Scope)

        if self.peek("INTEGER"):
            # lobster-trace: LRM.Integer_Values
            self.match("INTEGER")
            int_lit = ast.Integer_Literal(self.ct, self.builtin_int)
            int_lit.set_ast_link(self.ct)
            return int_lit

        elif self.peek("DECIMAL"):
            # lobster-trace: LRM.Decimal_Values
            self.match("DECIMAL")
            dec_lit = ast.Decimal_Literal(self.ct, self.builtin_decimal)
            dec_lit.set_ast_link(self.ct)
            return dec_lit

        elif self.peek("STRING"):
            # lobster-trace: LRM.String_Values
            self.match("STRING")
            string_lit = ast.String_Literal(self.ct, self.builtin_str)
            string_lit.set_ast_link(self.ct)
            return string_lit

        elif self.peek_kw("true") or self.peek_kw("false"):
            # lobster-trace: LRM.Boolean_Values
            self.match("KEYWORD")
            bool_lit = ast.Boolean_Literal(self.ct, self.builtin_bool)
            bool_lit.set_ast_link(self.ct)
            return bool_lit

        elif self.peek_kw("null"):
            self.match_kw("null")
            null_lit = ast.Null_Literal(self.ct)
            null_lit.set_ast_link(self.ct)
            return null_lit

        elif self.peek("BRA"):
            self.match("BRA")
            t_bra = self.ct
            if self.peek_kw("forall") or self.peek_kw("exists"):
                rv = self.parse_quantified_expression(scope)
            elif self.peek_kw("if"):
                rv = self.parse_conditional_expression(scope)
            else:
                rv = self.parse_expression(scope)
            rv.set_ast_link(t_bra)
            self.match("KET")
            rv.set_ast_link(self.ct)
            return rv

        else:
            return self.parse_name(scope)

    def parse_quantified_expression(self, scope):
        # lobster-trace: LRM.Quantified_Expression
        assert isinstance(scope, ast.Scope)

        if self.peek_kw("forall"):
            self.match_kw("forall")
            t_quantified = self.ct
            universal = True
        else:
            self.match_kw("exists")
            t_quantified = self.ct
            universal = False
        loc = self.ct.location
        self.match("IDENTIFIER")
        t_qv = self.ct
        if scope.contains(t_qv.value):
            # lobster-trace: LRM.Quantification_Naming_Scope
            pdef = scope.lookup(self.mh, t_qv)
            self.mh.error(t_qv.location,
                          "shadows %s %s from %s" %
                          (pdef.__class__.__name__,
                           pdef.name,
                           self.mh.cross_file_reference(pdef.location)))
        self.match_kw("in")
        t_in = self.ct
        self.match("IDENTIFIER")
        field = scope.lookup(self.mh, self.ct, ast.Composite_Component)
        n_source = ast.Name_Reference(self.ct.location,
                                      field)
        n_source.set_ast_link(self.ct)
        if not isinstance(field.n_typ, ast.Array_Type):
            # lobster-trace: LRM.Quantification_Object
            self.mh.error(self.ct.location,
                          "you can only quantify over arrays")
        n_var = ast.Quantified_Variable(t_qv.value,
                                        t_qv.location,
                                        field.n_typ.element_type)
        n_var.set_ast_link(t_qv)
        self.match("ARROW")
        t_arrow = self.ct

        new_table = ast.Symbol_Table()
        new_table.register(self.mh, n_var)
        scope.push(new_table)
        n_expr = self.parse_expression(scope)
        scope.pop()

        quantified_expression = ast.Quantified_Expression(
            mh         = self.mh,
            location   = loc,
            typ        = self.builtin_bool,
            universal  = universal,
            n_variable = n_var,
            n_source   = n_source,
            n_expr     = n_expr)

        quantified_expression.set_ast_link(t_quantified)
        quantified_expression.set_ast_link(t_in)
        quantified_expression.set_ast_link(t_arrow)

        return quantified_expression

    def parse_conditional_expression(self, scope):
        # lobster-trace: LRM.Conditional_Expression
        # lobster-trace: LRM.Restricted_Null
        assert isinstance(scope, ast.Scope)

        self.match_kw("if")
        t_if = self.ct
        if_cond = self.parse_expression(scope)
        self.match_kw("then")
        t_then = self.ct
        if_expr = self.parse_expression(scope)
        if if_expr.typ is None:
            self.mh.error(if_expr.location,
                          "null is not permitted here")
        if_action = ast.Action(self.mh, t_if, if_cond, if_expr)

        rv = ast.Conditional_Expression(location  = t_if.location,
                                        if_action = if_action)
        if_action.set_ast_link(t_if)
        if_action.set_ast_link(t_then)

        while self.peek_kw("elsif"):
            self.match_kw("elsif")
            t_elsif = self.ct
            elsif_cond = self.parse_expression(scope)
            self.match_kw("then")
            t_then = self.ct
            elsif_expr = self.parse_expression(scope)
            elsif_action = ast.Action(self.mh, t_elsif, elsif_cond, elsif_expr)
            elsif_action.set_ast_link(t_elsif)
            elsif_action.set_ast_link(t_then)
            rv.add_elsif(self.mh, elsif_action)

        self.match_kw("else")
        rv.set_ast_link(self.ct)
        else_expr = self.parse_expression(scope)
        rv.set_else_part(self.mh, else_expr)

        return rv

    def parse_builtin(self, scope, n_name, t_name):
        # lobster-trace: LRM.Builtin_Functions
        # lobster-trace: LRM.Builtin_Type_Conversion_Functions
        assert isinstance(scope, ast.Scope)
        assert isinstance(n_name, (ast.Builtin_Function,
                                   ast.Builtin_Numeric_Type))
        assert isinstance(t_name, Token)

        # Parse the arguments.
        parameters = []
        n_name.set_ast_link(self.ct)
        self.match("BRA")
        n_name.set_ast_link(self.ct)
        while not self.peek("KET"):
            exp = self.parse_expression(scope)
            if not self.ct.ast_link:
                exp.set_ast_link(self.ct)
            parameters.append(exp)

            if self.peek("COMMA"):
                self.match("COMMA")
                n_name.set_ast_link(self.ct)
            else:
                break
        self.match("KET")
        n_name.set_ast_link(self.ct)

        # Enforce arity
        if isinstance(n_name, ast.Builtin_Function):
            required_arity = n_name.arity
            precise        = not n_name.arity_at_least
        else:
            required_arity = 1
            precise        = True

        if precise:
            if required_arity != len(parameters):
                self.mh.error(t_name.location,
                              "function requires %u parameters" %
                              n_name.arity)
        else:
            if required_arity > len(parameters):
                self.mh.error(t_name.location,
                              "function requires at least %u parameters" %
                              n_name.arity)

        # Enforce types
        if n_name.name == "len":
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
                             "endswith"):
            return ast.Binary_Expression(
                mh       = self.mh,
                location = t_name.location,
                typ      = self.builtin_bool,
                operator = (ast.Binary_Operator.STRING_STARTSWITH
                            if "startswith" in n_name.name
                            else ast.Binary_Operator.STRING_ENDSWITH),
                n_lhs    = parameters[0],
                n_rhs    = parameters[1])

        elif n_name.name == "matches":
            parameters[1].ensure_type(self.mh, ast.Builtin_String)
            try:
                # lobster-trace: LRM.Static_Regular_Expression
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

        elif n_name.name == "oneof":
            return ast.OneOf_Expression(
                mh       = self.mh,
                location = t_name.location,
                typ      = self.builtin_bool,
                choices  = parameters)

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
        # lobster-trace: LRM.Names

        # This is a bit more complex. The grammar is:
        #
        # qualified_name ::= [ IDENTIFIER_package_name '.' ] IDENTIFIER_name
        #
        # name ::= qualified_name
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

        # lobster-trace: LRM.Builtin_Functions
        # lobster-trace: LRM.Builtin_Type_Conversion_Functions
        self.match("IDENTIFIER")
        if self.peek("BRA"):
            # If we follow our name with brackets
            # immediately, we have a builtin function call.
            n_name = self.stab.lookup(self.mh,
                                        self.ct)
            if not isinstance(n_name, (ast.Builtin_Function,
                                        ast.Builtin_Numeric_Type)):
                self.mh.error(self.ct.location,
                                "not a valid builtin function "
                                "or numeric type")
        else:
            n_name = self.parse_qualified_name(scope, match_ident=False)

        # Enum literals are a bit different, so we deal with them
        # first.
        if isinstance(n_name, ast.Enumeration_Type):
            n_name.set_ast_link(self.ct)
            self.match("DOT")
            n_name.set_ast_link(self.ct)
            self.match("IDENTIFIER")
            lit = n_name.literals.lookup(self.mh,
                                         self.ct,
                                         ast.Enumeration_Literal_Spec)
            enum_lit = ast.Enumeration_Literal(location = self.ct.location,
                                               literal  = lit)
            enum_lit.set_ast_link(self.ct)
            return enum_lit

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
            # lobster-trace: LRM.Builtin_Functions
            # lobster-trace: LRM.Builtin_Type_Conversion_Functions
            return self.parse_builtin(scope, n_name, self.ct)

        assert isinstance(n_name, (ast.Composite_Component,
                                   ast.Quantified_Variable))

        # We now process the potentially recursive part:
        #        | name '.' IDENTIFIER
        #        | name '[' expression ']'
        n_name = ast.Name_Reference(location = self.ct.location,
                                    entity   = n_name)
        n_name.set_ast_link(self.ct)
        while self.peek("DOT") or self.peek("S_BRA"):
            if self.peek("DOT"):
                if not isinstance(n_name.typ, ast.Tuple_Type):
                    # lobster-trace: LRM.Valid_Index_Prefixes
                    self.mh.error(n_name.location,
                                  "expression '%s' has type %s, "
                                  "which is not a tuple" %
                                  (n_name.to_string(),
                                   n_name.typ.name))
                self.match("DOT")
                t_dot = self.ct
                self.match("IDENTIFIER")
                n_field = n_name.typ.components.lookup(self.mh,
                                                       self.ct,
                                                       ast.Composite_Component)
                n_field.set_ast_link(self.ct)
                n_name = ast.Field_Access_Expression(
                    mh       = self.mh,
                    location = self.ct.location,
                    n_prefix = n_name,
                    n_field  = n_field)
                n_name.set_ast_link(t_dot)

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
                a_binary = ast.Binary_Operator.INDEX
                t_bracket.ast_link = a_binary
                self.ct.ast_link = a_binary

                n_name = ast.Binary_Expression(
                    mh       = self.mh,
                    location = t_bracket.location,
                    typ      = n_name.typ.element_type,
                    operator = a_binary,
                    n_lhs    = n_name,
                    n_rhs    = n_index)

        return n_name

    def parse_check_block(self):
        # lobster-trace: LRM.Check_Block
        t_severity = None
        self.match_kw("checks")
        t_checks = self.ct
        self.match("IDENTIFIER")
        # lobster-trace: LRM.Applicable_Types
        # lobster-trace: LRM.Applicable_Components
        n_ctype = self.cu.package.symbols.lookup(self.mh,
                                                 self.ct,
                                                 ast.Composite_Type)
        n_check_block = ast.Check_Block(location = self.ct.location,
                                        n_typ    = n_ctype)
        n_check_block.set_ast_link(t_checks)
        n_ctype.set_ast_link(self.ct)
        scope = ast.Scope()
        scope.push(self.stab)
        scope.push(self.cu.package.symbols)
        scope.push(n_ctype.components)
        self.match("C_BRA")
        n_check_block.set_ast_link(self.ct)
        while not self.peek("C_KET"):
            c_expr = self.parse_expression(scope)
            if not isinstance(c_expr.typ, ast.Builtin_Boolean):
                self.mh.error(c_expr.location,
                              "check expression must be Boolean")

            self.match("COMMA")
            t_first_comma = self.ct
            if self.peek("KEYWORD"):
                self.match("KEYWORD")
                t_severity = self.ct
                if self.ct.value not in ("warning", "error", "fatal"):
                    self.mh.error(self.ct.location,
                                  "expected warning|error|fatal")
                c_sev = self.ct.value
            else:
                c_sev = "error"

            self.match("STRING")
            if "\n" in self.ct.value:
                # lobster-trace: LRM.No_Newlines_In_Message
                self.mh.error(self.ct.location,
                              "error message must not contain a newline",
                              fatal = False)
            t_msg = self.ct

            has_extrainfo = False
            has_anchor    = False
            if self.peek("COMMA"):
                self.match("COMMA")
                t_second_comma = self.ct
                if self.peek("IDENTIFIER"):
                    has_anchor = True
                elif self.peek("STRING"):
                    has_extrainfo = True
                else:
                    self.mh.error(self.nt.location,
                                  "expected either a details string or"
                                  " identifier to anchor the check message")

            if has_extrainfo:
                self.match("STRING")
                t_extrainfo = self.ct
                c_extrainfo = self.ct.value

                if self.peek("COMMA"):
                    self.match("COMMA")
                    t_third_comma = self.ct
                    has_anchor = True

            else:
                c_extrainfo = None

            if has_anchor:
                self.match("IDENTIFIER")
                t_anchor = self.ct
                c_anchor = n_ctype.components.lookup(self.mh,
                                                     self.ct,
                                                     ast.Composite_Component)
            else:
                c_anchor = None

            n_check = ast.Check(n_type    = n_ctype,
                                n_expr    = c_expr,
                                n_anchor  = c_anchor,
                                severity  = c_sev,
                                t_message = t_msg,
                                extrainfo = c_extrainfo)

            # pylint: disable=possibly-used-before-assignment
            # pylint: disable=used-before-assignment

            n_check.set_ast_link(t_first_comma)
            if t_severity:
                n_check.set_ast_link(t_severity)
            n_check.set_ast_link(t_msg)
            if c_extrainfo or c_anchor:
                n_check.set_ast_link(t_second_comma)
            if c_extrainfo:
                n_check.set_ast_link(t_extrainfo)
            if c_anchor:
                c_anchor.set_ast_link(t_anchor)
            if c_anchor and c_extrainfo:
                n_check.set_ast_link(t_third_comma)

            n_ctype.add_check(n_check)
            n_check_block.add_check(n_check)

            assert scope.size() == 3

        self.match("C_KET")
        n_check_block.set_ast_link(self.ct)

        return n_check_block

    def parse_section_declaration(self):
        # lobster-trace: LRM.Section_Declaration
        self.match_kw("section")
        t_section = self.ct
        self.match("STRING")
        sec = ast.Section(name     = self.ct.value,
                          location = self.ct.location,
                          parent = self.section[-1] if self.section else None)
        sec.set_ast_link(self.ct)
        sec.set_ast_link(t_section)
        self.section.append(sec)
        self.match("C_BRA")
        sec.set_ast_link(self.ct)
        while not self.peek("C_KET"):
            self.parse_trlc_entry()
        self.match("C_KET")
        sec.set_ast_link(self.ct)
        self.section.pop()

    def parse_boolean(self):
        # lobster-trace: LRM.Boolean_Values
        self.match("KEYWORD")
        if self.ct.value in ("true", "false"):
            return ast.Boolean_Literal(self.ct, self.builtin_bool)
        else:
            self.mh.error(self.ct.location,
                          "expected boolean literal (true or false)")

    def parse_value(self, typ):
        # lobster-trace: LRM.Tuple_Syntax_Correct_Form
        assert isinstance(typ, ast.Type)

        if isinstance(typ, ast.Builtin_Numeric_Type):
            # lobster-trace: LRM.Integer_Values
            # lobster-trace: LRM.Decimal_Values
            if self.peek("OPERATOR") and \
               self.nt.value in Parser.ADDING_OPERATOR:
                self.match("OPERATOR")
                t_op = self.ct
                e_op = (ast.Unary_Operator.PLUS
                        if t_op.value == "+"
                        else ast.Unary_Operator.MINUS)
                t_op.ast_link = e_op
            else:
                t_op = None

            if isinstance(typ, ast.Builtin_Decimal):
                self.match("DECIMAL")
                rv = ast.Decimal_Literal(self.ct, self.builtin_decimal)
                rv.set_ast_link(self.ct)
            elif isinstance(typ, ast.Builtin_Integer):
                self.match("INTEGER")
                rv = ast.Integer_Literal(self.ct, self.builtin_int)
                rv.set_ast_link(self.ct)
            else:
                assert False

            if t_op:
                rv = ast.Unary_Expression(mh        = self.mh,
                                          location  = t_op.location,
                                          typ       = rv.typ,
                                          operator  = e_op,
                                          n_operand = rv)

            return rv

        elif isinstance(typ, ast.Builtin_Markup_String):
            # lobster-trace: LRM.Markup_String_Values
            return self.parse_markup_string()

        elif isinstance(typ, ast.Builtin_String):
            # lobster-trace: LRM.String_Values
            self.match("STRING")
            rv = ast.String_Literal(self.ct, self.builtin_str)
            rv.set_ast_link(self.ct)
            return rv

        elif isinstance(typ, ast.Builtin_Boolean):
            rv = self.parse_boolean()
            rv.set_ast_link(self.ct)
            return rv

        elif isinstance(typ, ast.Array_Type):
            self.match("S_BRA")
            rv = ast.Array_Aggregate(self.ct.location,
                                     typ)
            rv.set_ast_link(self.ct)
            while not self.peek("S_KET"):
                array_elem = self.parse_value(typ.element_type)
                rv.append(array_elem)
                if self.peek("COMMA"):
                    self.match("COMMA")
                    rv.set_ast_link(self.ct)
                elif self.peek("S_KET") or self.nt is None:
                    break
                else:
                    self.mh.error(self.ct.location,
                                  "comma separating array elements is "
                                  "missing",
                                  fatal = False)

            self.match("S_KET")
            rv.set_ast_link(self.ct)

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
            enum.set_ast_link(self.ct)
            if enum != typ:
                self.mh.error(self.ct.location,
                              "expected %s" % typ.name)
            self.match("DOT")
            enum.set_ast_link(self.ct)
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
                t_dot = self.ct
                self.match("IDENTIFIER")
                the_pkg = self.stab.lookup(self.mh, t_name, ast.Package)
                the_pkg.set_ast_link(t_name)
                the_pkg.set_ast_link(t_dot)
                if not self.cu.is_visible(the_pkg):
                    self.mh.error(self.ct.location,
                                  "package must be imported before use")
                t_name = self.ct
            else:
                the_pkg = self.cu.package

            rv = ast.Record_Reference(location = t_name.location,
                                      name     = t_name.value,
                                      typ      = typ,
                                      package  = the_pkg)
            rv.set_ast_link(t_name)

            # We can do an early lookup if the target is known
            if the_pkg.symbols.contains(t_name.value):
                rv.resolve_references(self.mh)

            return rv

        elif isinstance(typ, ast.Tuple_Type) and typ.has_separators():
            # lobster-trace: LRM.Tuple_Separator_Form
            rv = ast.Tuple_Aggregate(self.nt.location, typ)

            next_is_optional = False
            for n_item in typ.iter_sequence():
                if isinstance(n_item, ast.Composite_Component):
                    if next_is_optional and n_item.optional:
                        break
                    value = self.parse_value(n_item.n_typ)
                    rv.assign(n_item.name, value)

                elif n_item.token.kind in ("AT", "COLON", "SEMICOLON"):
                    if self.peek(n_item.token.kind):
                        self.match(n_item.token.kind)
                        n_item.set_ast_link(self.ct)
                    else:
                        next_is_optional = True

                elif n_item.token.kind == "IDENTIFIER":
                    if self.peek("IDENTIFIER") and \
                       self.nt.value == n_item.token.value:
                        self.match("IDENTIFIER")
                        n_item.set_ast_link(self.ct)
                    else:
                        next_is_optional = True

                else:
                    assert False

            return rv

        elif isinstance(typ, ast.Tuple_Type) and not typ.has_separators():
            # lobster-trace: LRM.Tuple_Generic_Form
            self.match("BRA")
            rv = ast.Tuple_Aggregate(self.ct.location, typ)
            rv.set_ast_link(self.ct)

            first = True
            for n_field in typ.iter_sequence():
                if first:
                    first = False
                else:
                    self.match("COMMA")
                    rv.set_ast_link(self.ct)
                rv.assign(n_field.name,
                          self.parse_value(n_field.n_typ))

            self.match("KET")
            rv.set_ast_link(self.ct)
            return rv

        else:
            self.mh.ice_loc(self.ct.location,
                            "logic error: unexpected type %s" %
                            typ.__class__.__name__)

    def parse_markup_string(self):
        # lobster-trace: LRM.Markup_String_Values
        self.match("STRING")
        rv = ast.String_Literal(self.ct, self.builtin_mstr)
        mpar = Markup_Parser(self, rv)
        mpar.parse_all_references()
        return rv

    def parse_record_object_declaration(self):
        # lobster-trace: LRM.Section_Declaration
        # lobster-trace: LRM.Record_Object_Declaration
        # lobster-trace: LRM.Valid_Record_Types
        # lobster-trace: LRM.Valid_Components
        # lobster-trace: LRM.Valid_Enumeration_Literals
        # lobster-trace: LRM.Mandatory_Components
        # lobster-trace: LRM.Evaluation_Of_Checks
        # lobster-trace: LRM.Single_Value_Assignment

        r_typ = self.parse_qualified_name(self.default_scope,
                                          ast.Record_Type)
        r_typ.set_ast_link(self.ct)
        if r_typ.is_abstract:
            self.mh.error(self.ct.location,
                          "cannot declare object of abstract record type %s" %
                          r_typ.name)

        self.match("IDENTIFIER")
        obj = ast.Record_Object(
            name      = self.ct.value,
            location  = self.ct.location,
            n_typ     = r_typ,
            section   = self.section.copy() if self.section else None,
            n_package = self.cu.package)
        self.cu.package.symbols.register(self.mh, obj)
        obj.set_ast_link(self.ct)

        self.match("C_BRA")
        obj.set_ast_link(self.ct)
        while not self.peek("C_KET"):
            self.match("IDENTIFIER")
            comp = r_typ.components.lookup(self.mh,
                                           self.ct,
                                           ast.Composite_Component)
            if obj.is_component_implicit_null(comp):
                self.mh.error(self.ct.location,
                              "component '%s' already assigned at line %i" %
                              (comp.name,
                               obj.field[comp.name].location.line_no))
            comp.set_ast_link(self.ct)
            if r_typ.is_frozen(comp):
                self.mh.error(self.ct.location,
                              "cannot overwrite frozen component %s" %
                              comp.name)
            self.match("ASSIGN")
            comp.set_ast_link(self.ct)
            value = self.parse_value(comp.n_typ)
            if not self.ct.ast_link:
                value.set_ast_link(self.ct)
            obj.assign(comp, value)

        # Check that each non-optional component has been specified
        for comp in r_typ.all_components():
            if isinstance(obj.field[comp.name], ast.Implicit_Null):
                if r_typ.is_frozen(comp):
                    obj.assign(comp, r_typ.get_freezing_expression(comp))
                elif not comp.optional:
                    self.mh.error(
                        obj.location,
                        "required component %s (see %s) is not defined" %
                        (comp.name,
                         self.mh.cross_file_reference(comp.location)))

        self.match("C_KET")
        obj.set_ast_link(self.ct)

        return obj

    def parse_trlc_entry(self):
        # lobster-trace: LRM.TRLC_File
        if self.peek_kw("section"):
            self.parse_section_declaration()
        else:
            self.cu.add_item(self.parse_record_object_declaration())

    def parse_preamble(self, kind):
        assert kind in ("rsl", "trlc")
        # lobster-trace: LRM.Layout
        # lobster-trace: LRM.Preamble

        # First, parse package indication, declaring the package if
        # needed
        self.match_kw("package")
        t_pkg = self.ct
        self.match("IDENTIFIER")

        if kind == "rsl":
            declare_package = True
        else:
            # lobster-trace: LRM.Late_Package_Declarations
            declare_package = not self.stab.contains(self.ct.value)

        if declare_package:
            # lobster-trace: LRM.Package_Declaration
            pkg = ast.Package(name          = self.ct.value,
                              location      = self.ct.location,
                              builtin_stab  = self.stab,
                              declared_late = kind == "trlc")
            self.stab.register(self.mh, pkg)
        else:
            pkg = self.stab.lookup(self.mh, self.ct, ast.Package)

        pkg.set_ast_link(t_pkg)
        pkg.set_ast_link(self.ct)

        # lobster-trace: LRM.Current_Package
        self.cu.set_package(pkg)

        self.default_scope.push(self.cu.package.symbols)

        # Second, parse import list (but don't resolve names yet)
        # lobster-trace: LRM.Import_Visibility
        if kind != "check":
            while self.peek_kw("import"):
                self.match_kw("import")
                pkg.set_ast_link(self.ct)
                self.match("IDENTIFIER")
                self.cu.add_import(self.mh, self.ct)

    def parse_rsl_file(self):
        # lobster-trace: LRM.RSL_File
        assert self.cu.package is not None

        ok = True
        while not self.peek_eof():
            try:
                if self.peek_kw("checks"):
                    self.cu.add_item(self.parse_check_block())
                else:
                    self.cu.add_item(self.parse_type_declaration())
            except TRLC_Error as err:
                if not self.error_recovery or err.kind == "lex error":
                    raise

                ok = False

                # Recovery strategy is to scan until we get the next
                # relevant keyword
                self.skip_until_newline()
                while not self.peek_eof():
                    if self.peek_kw("checks") or \
                       self.peek_kw("type") or \
                       self.peek_kw("abstract") or \
                       self.peek_kw("final") or \
                       self.peek_kw("tuple") or \
                       self.peek_kw("enum"):
                        break
                    self.advance()
                    self.skip_until_newline()

        self.match_eof()

        for tok in self.lexer.tokens:
            if tok.kind == "COMMENT":
                self.cu.package.set_ast_link(tok)

        return ok

    def parse_trlc_file(self):
        # lobster-trace: LRM.TRLC_File
        assert self.cu.package is not None

        ok = True

        while self.peek_kw("section") or self.peek("IDENTIFIER"):
            try:
                self.parse_trlc_entry()
            except TRLC_Error as err:
                if not self.error_recovery or err.kind == "lex error":
                    raise

                ok = False

                # Recovery strategy is to keep going until we find an
                # identifier that is a package or type, or section, or
                # EOF
                self.skip_until_newline()
                while not self.peek_eof():
                    if self.peek_kw("section"):
                        break
                    elif not self.peek("IDENTIFIER"):
                        pass
                    elif self.stab.contains(self.nt.value):
                        n_sym = self.stab.lookup_assuming(self.mh,
                                                          self.nt.value)
                        if isinstance(n_sym, ast.Package):
                            break
                    elif self.cu.package.symbols.contains(self.nt.value):
                        n_sym = self.cu.package.symbols.lookup_assuming(
                            self.mh,
                            self.nt.value)
                        if isinstance(n_sym, ast.Record_Type):
                            break
                    self.advance()
                    self.skip_until_newline()

        self.match_eof()

        for tok in self.lexer.tokens:
            if tok.kind == "COMMENT":
                self.cu.package.set_ast_link(tok)

        return ok
