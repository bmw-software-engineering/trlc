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
    assert isinstance(raw_value, str)
    assert raw_value.startswith("'''")
    assert raw_value.endswith("'''")

    lines = raw_value[3:-3].strip().splitlines()
    if not lines:
        return ""

    non_empty_lines = [line for line in lines if line.strip()]

    value      = lines[0]
    common_ws  = ""
    common_len = 0
    if len(non_empty_lines) >= 2:
        for c in non_empty_lines[1]:
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


class Token_Base:
    def __init__(self, location, kind, value):
        assert isinstance(location, Location)
        assert isinstance(kind, str)
        self.location = location
        self.kind     = kind
        self.value    = value


class Token(Token_Base):
    KIND = frozenset(["COMMENT",
                      "IDENTIFIER",
                      "BUILTIN",
                      "KEYWORD",
                      "BRA", "KET",
                      "S_BRA", "S_KET",
                      "C_BRA", "C_KET",
                      "AT",
                      "COMMA",
                      "SEMICOLON",
                      "COLON",
                      "DOT",
                      "RANGE",
                      "ASSIGN",
                      "OPERATOR",
                      "ARROW",
                      "INTEGER",
                      "DECIMAL",
                      "STRING"])

    def __init__(self, location, kind, value=None):
        assert kind in Token.KIND
        if kind in ("COMMENT", "IDENTIFIER", "BUILTIN",
                    "KEYWORD", "OPERATOR", "STRING"):
            assert isinstance(value, str)
        elif kind == "INTEGER":
            assert isinstance(value, int)
        elif kind == "DECIMAL":
            assert isinstance(value, Fraction)
        else:
            assert value is None
        super().__init__(location, kind, value)

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

        self.lexpos = -3
        self.line_no = 0
        self.col_no  = 0
        self.cc  = None
        self.nc  = None
        self.nnc = None

        self.advance()
        self.advance()

    @staticmethod
    def is_alpha(char):
        assert isinstance(char, str) and len(char) == 1
        return ord('a') <= ord(char) <= ord('z') or \
            ord('A') <= ord(char) <= ord('Z')

    @staticmethod
    def is_numeric(char):
        assert isinstance(char, str) and len(char) == 1
        return ord('0') <= ord(char) <= ord('9')

    @staticmethod
    def is_alnum(char):
        assert isinstance(char, str) and len(char) == 1
        return ord('a') <= ord(char) <= ord('z') or \
            ord('A') <= ord(char) <= ord('Z') or \
            ord('0') <= ord(char) <= ord('9')

    @abstractmethod
    def file_location(self):
        pass

    @abstractmethod
    def token(self):
        pass

    def skip_whitespace(self):
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
        if file_content:
            super().__init__(mh, file_content)
        else:
            with open(file_name, "r", encoding="UTF-8") as fd:
                super().__init__(mh, fd.read())
        self.file_name = file_name

    def current_location(self):
        return Source_Reference(lexer      = self,
                                start_line = self.line_no,
                                start_col  = self.col_no,
                                start_pos  = self.lexpos,
                                end_pos    = self.lexpos)

    def file_location(self):
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
            kind = "COMMENT"
            while self.cc and self.nc != "\n":
                self.advance()

        elif self.cc == "/" and self.nc == "*":
            kind = "COMMENT"
            while self.nc and not (self.cc == "*" and self.nc == "/"):
                self.advance()
            self.advance()

        elif self.is_alpha(self.cc):
            kind = "IDENTIFIER"
            while self.nc and (self.is_alnum(self.nc) or
                               self.nc == "_" or
                               self.nc == ":"):
                self.advance()

        elif self.cc in TRLC_Lexer.PUNCTUATION:
            kind = TRLC_Lexer.PUNCTUATION[self.cc]

        elif self.cc == "=":
            if self.nc == ">":
                kind = "ARROW"
                self.advance()
            elif self.nc == "=":
                kind = "OPERATOR"
                self.advance()
            else:
                kind = "ASSIGN"

        elif self.cc == ".":
            if self.nc == ".":
                kind = "RANGE"
                self.advance()
            else:
                kind = "DOT"

        elif self.cc in ("<", ">"):
            kind = "OPERATOR"
            if self.nc == "=":
                self.advance()

        elif self.cc == "!":
            kind = "OPERATOR"
            if self.nc == "=":
                self.advance()
            else:
                self.mh.lex_error(self.current_location(),
                                  "malformed != operator")

        elif self.cc == "*":
            kind = "OPERATOR"
            if self.nc == "*":
                self.advance()

        elif self.cc == '"':
            kind = "STRING"
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
            kind = "INTEGER"
            while self.nc and self.is_numeric(self.nc):
                self.advance()

            if self.nc == "." and self.nnc != ".":
                kind = "DECIMAL"
                self.advance()
                if not self.nc or not self.is_numeric(self.nc):
                    self.mh.lex_error(
                        Source_Reference(lexer      = self,
                                         start_line = start_line,
                                         start_col  = start_col,
                                         start_pos  = start_pos,
                                         end_pos    = self.lexpos),
                        "unfinished decimal number")
                while self.nc and self.is_numeric(self.nc):
                    self.advance()

        else:
            self.mh.lex_error(self.current_location(),
                              "unexpected character '%s'" % self.cc)

        sref = Source_Reference(lexer      = self,
                                start_line = start_line,
                                start_col  = start_col,
                                start_pos  = start_pos,
                                end_pos    = self.lexpos)

        if kind == "IDENTIFIER":
            value = sref.text()
            if value in TRLC_Lexer.KEYWORDS:
                kind = "KEYWORD"
            elif ":" in value:
                kind = "BUILTIN"
                if not value.startswith("trlc:"):
                    self.mh.lex_error(sref,
                                      "builtin function name must start "
                                      "with trlc:")

        elif kind == "OPERATOR":
            value = sref.text()

        elif kind == "STRING":
            value = sref.text()
            if value.startswith('"'):
                value = value[1:-1]
                value = value.replace('\\"', '"')
            else:
                value = triple_quoted_string_value(value)

        elif kind == "INTEGER":
            value = int(sref.text())

        elif kind == "DECIMAL":
            value = Fraction(sref.text())

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


def sanity_test():
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
