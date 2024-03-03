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

import sys
from fractions import Fraction
from abc import ABCMeta, abstractmethod

from trlc.errors import Location, Message_Handler


def triple_quoted_string_value(raw_value):
    # lobster-trace: LRM.Complex_String_Value
    assert isinstance(raw_value, str)
    assert len(raw_value) >= 6
    assert raw_value.startswith("'''") or raw_value.startswith('"""')
    assert raw_value[:3] == raw_value[-3:]

    lines = raw_value[3:-3].strip().splitlines()
    if not lines:
        return ""

    non_empty_lines = [line for line in lines if line.strip()]

    value      = lines[0]
    common_ws  = ""
    common_len = 0
    if len(non_empty_lines) >= 2:
        # The loop below cannot complete by construction
        for c in non_empty_lines[1]:  # pragma: no cover
            if c not in (" \t"):
                break
            common_ws  += c
            common_len += 1
    else:
        return value

    for line in lines[2:]:
        if not line.strip():
            continue
        for idx in range(common_len):
            if idx < len(line) and line[idx] == common_ws[idx]:
                pass
            else:
                common_len = idx
                break

    for line in lines[1:]:
        value += "\n" + line[common_len:].rstrip()

    return value


class Source_Reference(Location):
    def __init__(self, lexer, start_line, start_col, start_pos, end_pos):
        assert isinstance(lexer, TRLC_Lexer)
        assert isinstance(start_line, int)
        assert isinstance(start_col, int)
        assert isinstance(start_pos, int)
        assert isinstance(end_pos, int)
        assert 0 <= start_pos <= end_pos < lexer.length
        super().__init__(lexer.file_name,
                         start_line,
                         start_col)
        self.lexer     = lexer
        self.start_pos = start_pos
        self.end_pos   = end_pos

    def text(self):
        return self.lexer.content[self.start_pos:self.end_pos + 1]

    def context_lines(self):
        line = ""
        n = self.start_pos
        while n >= 0:
            if self.lexer.content[n] == "\n":
                break
            line = self.lexer.content[n] + line
            n -= 1
        offset = self.start_pos - n - 1
        n = self.start_pos + 1
        while n < self.lexer.length:
            if self.lexer.content[n] == "\n":
                break
            line = line + self.lexer.content[n]
            n += 1
        maxtrail = n - self.start_pos
        tlen = self.end_pos + 1 - self.start_pos

        stripped_line = line.lstrip()
        stripped_offset = offset - (len(line) - len(stripped_line))

        return [stripped_line,
                " " * stripped_offset + "^" * min(tlen, maxtrail)]

    def get_end_location(self):
        lines_in_between = self.lexer.content[
            self.start_pos : self.end_pos + 1
        ].count("\n")
        end_line = self.line_no + lines_in_between

        end_col = self.end_pos + 1
        for n in range(self.end_pos, 1, -1):
            if self.lexer.content[n] == "\n":
                end_col = max(self.end_pos - n, 1)
                break

        return Location(self.file_name, end_line, end_col)


class Token_Base:
    def __init__(self, location, kind, value):
        assert isinstance(location, Location)
        assert isinstance(kind, str)
        self.location = location
        self.kind     = kind
        self.value    = value


class Token(Token_Base):
    KIND = {
        "COMMENT"    : "comment",
        "IDENTIFIER" : "identifier",
        "KEYWORD"    : "keyword",
        "BRA"        : "opening parenthesis '('",
        "KET"        : "closing parenthesis ')'",
        "S_BRA"      : "opening bracket '['",
        "S_KET"      : "closing bracket ']'",
        "C_BRA"      : "opening brace '{'",
        "C_KET"      : "closing brace '}'",
        "COMMA"      : "comma ','",
        "AT"         : "separtor '@'",
        "SEMICOLON"  : "separator ';'",
        "COLON"      : "separator ':'",
        "DOT"        : ".",
        "RANGE"      : "..",
        "ASSIGN"     : "=",
        "OPERATOR"   : "operator",
        "ARROW"      : "->",
        "INTEGER"    : "integer literal",
        "DECIMAL"    : "decimal literal",
        "STRING"     : "string literal",
    }

    def __init__(self, location, kind, value=None, ast_link=None):
        assert kind in Token.KIND
        if kind in ("COMMENT", "IDENTIFIER",
                    "KEYWORD", "OPERATOR", "STRING"):
            assert isinstance(value, str)
        elif kind == "INTEGER":
            assert isinstance(value, int)
        elif kind == "DECIMAL":
            assert isinstance(value, Fraction)
        else:
            assert value is None
        super().__init__(location, kind, value)
        self.ast_link = ast_link

    def __repr__(self):
        if self.value is None:
            return "%s_Token" % self.kind
        else:
            return "%s_Token(%s)" % (self.kind, self.value)


class Lexer_Base(metaclass=ABCMeta):
    def __init__(self, mh, content):
        assert isinstance(mh, Message_Handler)
        assert isinstance(content, str)
        self.mh        = mh
        self.content   = content
        self.length    = len(self.content)
        self.tokens    = []

        self.lexpos  = -3
        self.line_no = 0
        self.col_no  = 0
        self.cc  = None
        self.nc  = None
        self.nnc = None

        self.advance()
        self.advance()

    @staticmethod
    def is_alpha(char):
        # lobster-trace: LRM.Identifier
        return char.isascii() and char.isalpha()

    @staticmethod
    def is_numeric(char):
        # lobster-trace: LRM.Integers
        # lobster-trace: LRM.Decimals
        return char.isascii() and char.isdigit()

    @staticmethod
    def is_alnum(char):
        # lobster-trace: LRM.Identifier
        return char.isascii() and char.isalnum()

    @abstractmethod
    def file_location(self):
        pass

    @abstractmethod
    def token(self):
        pass

    def skip_whitespace(self):
        # lobster-trace: LRM.Whitespace
        while self.nc and self.nc.isspace():
            self.advance()
        self.advance()

    def advance(self):
        self.lexpos += 1
        if self.cc == "\n" or self.lexpos == 0:
            self.line_no += 1
            self.col_no = 0
        if self.nc is not None:
            self.col_no += 1
        self.cc = self.nc
        self.nc = self.nnc
        self.nnc = (self.content[self.lexpos + 2]
                    if self.lexpos + 2 < self.length
                    else None)


class TRLC_Lexer(Lexer_Base):
    KEYWORDS = frozenset([
        "abs",
        "abstract",
        "and",
        "checks",
        "else",
        "elsif",
        "enum",
        "error",
        "exists",
        "extends",
        "false",
        "fatal",
        "final",
        "forall",
        "freeze",
        "if",
        "implies",
        "import",
        "in",
        "not",
        "null",
        "optional",
        "or",
        "package",
        "section",
        "separator",
        "then",
        "true",
        "tuple",
        "type",
        "warning",
        "xor"
    ])

    PUNCTUATION = {
        "(" : "BRA",
        ")" : "KET",
        "{" : "C_BRA",
        "}" : "C_KET",
        "[" : "S_BRA",
        "]" : "S_KET",
        "," : "COMMA",
        "@" : "AT",
        ":" : "COLON",
        ";" : "SEMICOLON",
        "/" : "OPERATOR",
        "%" : "OPERATOR",
        "+" : "OPERATOR",
        "-" : "OPERATOR",
    }

    def __init__(self, mh, file_name, file_content=None):
        assert isinstance(file_name, str)
        assert isinstance(file_content, str) or file_content is None
        self.file_name = file_name
        if file_content is None:
            # lobster-trace: LRM.File_Encoding
            # lobster-trace: LRM.File_Encoding_Fixed
            with open(file_name, "r", encoding="UTF-8") as fd:
                try:
                    super().__init__(mh, fd.read())
                except UnicodeDecodeError as err:
                    mh.lex_error(Location(file_name), str(err))
        else:
            super().__init__(mh, file_content)

    def current_location(self):
        # lobster-exclude: Utility function
        return Source_Reference(lexer      = self,
                                start_line = self.line_no,
                                start_col  = self.col_no,
                                start_pos  = self.lexpos,
                                end_pos    = self.lexpos)

    def file_location(self):
        # lobster-exclude: Utility function
        return Location(self.file_name, 1, 1)

    def token(self):
        # Skip whitespace and move to the next char
        self.skip_whitespace()

        # Return if we're done
        if self.cc is None:
            return None

        start_pos  = self.lexpos
        start_line = self.line_no
        start_col  = self.col_no

        if self.cc == "/" and self.nc == "/":
            # lobster-trace: LRM.Comments
            kind = "COMMENT"
            while self.cc and self.nc != "\n":
                self.advance()

        elif self.cc == "/" and self.nc == "*":
            # lobster-trace: LRM.Comments
            kind = "COMMENT"
            while self.nc and not (self.cc == "*" and self.nc == "/"):
                self.advance()
            self.advance()

        elif self.is_alpha(self.cc):
            # lobster-trace: LRM.Identifier
            kind = "IDENTIFIER"
            while self.nc and (self.is_alnum(self.nc) or
                               self.nc == "_"):
                self.advance()

        elif self.cc in TRLC_Lexer.PUNCTUATION:
            # lobster-trace: LRM.Single_Delimiters
            kind = TRLC_Lexer.PUNCTUATION[self.cc]

        elif self.cc == "=":
            # lobster-trace: LRM.Single_Delimiters
            # lobster-trace: LRM.Double_Delimiters
            # lobster-trace: LRM.Lexing_Disambiguation
            if self.nc == ">":
                kind = "ARROW"
                self.advance()
            elif self.nc == "=":
                kind = "OPERATOR"
                self.advance()
            else:
                kind = "ASSIGN"

        elif self.cc == ".":
            # lobster-trace: LRM.Single_Delimiters
            # lobster-trace: LRM.Double_Delimiters
            # lobster-trace: LRM.Lexing_Disambiguation
            if self.nc == ".":
                kind = "RANGE"
                self.advance()
            else:
                kind = "DOT"

        elif self.cc in ("<", ">"):
            # lobster-trace: LRM.Single_Delimiters
            # lobster-trace: LRM.Double_Delimiters
            # lobster-trace: LRM.Lexing_Disambiguation
            kind = "OPERATOR"
            if self.nc == "=":
                self.advance()

        elif self.cc == "!":
            # lobster-trace: LRM.Double_Delimiters
            # lobster-trace: LRM.Lexing_Disambiguation
            kind = "OPERATOR"
            if self.nc == "=":
                self.advance()
            else:
                self.mh.lex_error(self.current_location(),
                                  "malformed != operator")

        elif self.cc == "*":
            # lobster-trace: LRM.Single_Delimiters
            # lobster-trace: LRM.Double_Delimiters
            # lobster-trace: LRM.Lexing_Disambiguation
            kind = "OPERATOR"
            if self.nc == "*":
                self.advance()

        elif self.cc == '"':
            # lobster-trace: LRM.Strings
            kind = "STRING"
            if self.nc == '"' and self.nnc == '"':
                self.advance()
                self.advance()
                quotes_seen = 0
                while quotes_seen < 3:
                    self.advance()
                    if self.cc == '"':
                        quotes_seen += 1
                    else:
                        quotes_seen = 0
                    if self.nc is None:
                        self.mh.lex_error(
                            Source_Reference(lexer      = self,
                                             start_line = start_line,
                                             start_col  = start_col,
                                             start_pos  = start_pos,
                                             end_pos    = self.lexpos),
                            "unterminated triple-quoted string")
            else:
                while self.nc != '"':
                    if self.nc is None:
                        self.mh.lex_error(
                            Source_Reference(lexer      = self,
                                             start_line = start_line,
                                             start_col  = start_col,
                                             start_pos  = start_pos,
                                             end_pos    = self.lexpos),
                            "unterminated string")
                    elif self.nc == "\n":
                        self.mh.lex_error(
                            Source_Reference(lexer      = self,
                                             start_line = start_line,
                                             start_col  = start_col,
                                             start_pos  = start_pos,
                                             end_pos    = self.lexpos),
                            "double quoted strings cannot include newlines")

                    self.advance()
                    if self.cc == "\\" and self.nc == '"':
                        self.advance()
                self.advance()

        elif self.cc == "'":
            # lobster-trace: LRM.Strings
            kind = "STRING"
            for _ in range(2):
                self.advance()
                if self.cc != "'":
                    self.mh.lex_error(
                        Source_Reference(lexer      = self,
                                         start_line = start_line,
                                         start_col  = start_col,
                                         start_pos  = start_pos,
                                         end_pos    = self.lexpos),
                        "malformed triple-quoted string")
            quotes_seen = 0
            while quotes_seen < 3:
                self.advance()
                if self.cc == "'":
                    quotes_seen += 1
                else:
                    quotes_seen = 0
                if self.nc is None:
                    self.mh.lex_error(
                        Source_Reference(lexer      = self,
                                         start_line = start_line,
                                         start_col  = start_col,
                                         start_pos  = start_pos,
                                         end_pos    = self.lexpos),
                        "unterminated triple-quoted string")

        elif self.is_numeric(self.cc):
            # lobster-trace: LRM.Integers
            # lobster-trace: LRM.Decimals
            kind = "INTEGER"

            if self.cc == "0" and self.nc == "b":
                digits_allowed   = "01"
                digits_forbidden = "23456789abcdefABCDEF"
                int_base         = 2
                require_digit    = True
                decimal_allowed  = False
                self.advance()
            elif self.cc == "0" and self.nc == "x":
                digits_allowed   = "0123456789abcdefABCDEF"
                digits_forbidden = ""
                int_base         = 16
                require_digit    = True
                decimal_allowed  = False
                self.advance()
            else:
                digits_allowed   = "0123456789"
                digits_forbidden = "abcdefABCDEF"
                int_base         = 10
                require_digit    = False
                decimal_allowed  = True

            while self.nc:
                if self.nc in digits_allowed:
                    self.advance()
                    require_digit = False

                elif self.nc in digits_forbidden:
                    self.mh.lex_error(
                        Source_Reference(lexer      = self,
                                         start_line = start_line,
                                         start_col  = start_col,
                                         start_pos  = self.lexpos + 1,
                                         end_pos    = self.lexpos + 1),
                        "%s is not a valid base %u digit" % (self.nc,
                                                             int_base))

                elif require_digit:
                    self.mh.lex_error(
                        Source_Reference(lexer      = self,
                                         start_line = start_line,
                                         start_col  = start_col,
                                         start_pos  = self.lexpos + 1,
                                         end_pos    = self.lexpos + 1),
                        "base %u digit is required here" % int_base)

                elif self.nc == "_":
                    self.advance()
                    require_digit = True

                elif self.nc == "." and self.nnc == ".":
                    # This is a range token, so that one can't be part
                    # of our number anymore
                    break

                elif self.nc == ".":
                    self.advance()
                    if not decimal_allowed:
                        if int_base == 10:
                            msg = "decimal point is not allowed here"
                        else:
                            msg = ("base %u integer may not contain a"
                                   " decimal point" % int_base)
                        self.mh.lex_error(
                            Source_Reference(lexer      = self,
                                             start_line = start_line,
                                             start_col  = start_col,
                                             start_pos  = self.lexpos,
                                             end_pos    = self.lexpos),
                            msg)
                    decimal_allowed   = False
                    require_digit     = True
                    kind              = "DECIMAL"

                else:  # pragma: no cover
                    # This is actually a false
                    # alarm, this line is covered (it's the only
                    # normal way to exit this loop.
                    break

            if require_digit:
                self.mh.lex_error(
                    Source_Reference(lexer      = self,
                                     start_line = start_line,
                                     start_col  = start_col,
                                     start_pos  = start_pos,
                                     end_pos    = self.lexpos),
                    "unfinished base %u integer" % int_base)

        else:
            self.mh.lex_error(self.current_location(),
                              "unexpected character '%s'" % self.cc)

        sref = Source_Reference(lexer      = self,
                                start_line = start_line,
                                start_col  = start_col,
                                start_pos  = start_pos,
                                end_pos    = min(self.lexpos, self.length - 1))

        if kind == "IDENTIFIER":
            value = sref.text()
            if value in TRLC_Lexer.KEYWORDS:
                # lobster-trace: LRM.TRLC_Keywords
                kind = "KEYWORD"

        elif kind == "OPERATOR":
            value = sref.text()

        elif kind == "STRING":
            value = sref.text()
            if value.startswith('"""'):
                value = triple_quoted_string_value(value)
            elif value.startswith('"'):
                # lobster-trace: LRM.Simple_String_Value
                value = value[1:-1]
                value = value.replace('\\"', '"')
            else:
                value = triple_quoted_string_value(value)

        elif kind == "INTEGER":
            # lobster-trace: LRM.Integer_Values
            base_text = sref.text().replace("_", "")
            if int_base == 10:
                value = int(base_text)
            elif int_base == 2:
                value = int(base_text[2:], base=2)
            else:
                value = int(base_text[2:], base=16)

        elif kind == "DECIMAL":
            # lobster-trace: LRM.Decimal_Values
            value = Fraction(sref.text().replace("_", ""))

        elif kind == "COMMENT":
            value = sref.text()
            if value.startswith("//"):
                value = value[2:].strip()
            else:
                value = value[2:]
                if value.endswith("*/"):
                    value = value[:-2]
                value = value.strip()

        else:
            value = None

        return Token(sref, kind, value)


class Token_Stream(TRLC_Lexer):

    def token(self):
        tok = super().token()
        if tok is not None:
            self.tokens.append(tok)
        return tok


def sanity_test():
    # lobster-exclude: Developer test function
    mh    = Message_Handler()
    lexer = TRLC_Lexer(mh, sys.argv[1])

    while True:
        token  = lexer.token()
        if token is None:
            break
        mh.warning(token.location,
                   str(token))


if __name__ == "__main__":
    sanity_test()
