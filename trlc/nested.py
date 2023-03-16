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

from abc import abstractmethod

from trlc.ast import String_Literal
from trlc.lexer import Lexer_Base, Source_Reference


class Nested_Lexer(Lexer_Base):
    def __init__(self, mh, literal):
        assert isinstance(literal, String_Literal)

        origin_full_text = literal.location.text()
        self.origin_normal_string = origin_full_text.startswith('"')
        if self.origin_normal_string:
            self.base_offset = 1
            text = origin_full_text[1:-1].replace('\\"', '"')
        else:
            self.base_offset = 3
            text = origin_full_text[3:-3]

        self.origin_location = literal.location

        super().__init__(mh, text)

    def source_location(self, start_line, start_col, begin, end):
        assert 0 <= begin <= end < self.length
        assert start_line >= 1
        assert start_col >= 1

        if self.origin_normal_string:
            escapes_to_start = self.content[0:begin].count('"')
            escapes_to_end = escapes_to_start + \
                self.content[begin:end + 1].count('"')
            assert start_line == 1
            loc = Source_Reference(
                lexer      = self.origin_location.lexer,
                start_line = self.origin_location.line_no,
                start_col  = (self.origin_location.col_no +
                              self.base_offset +
                              begin + escapes_to_start),
                start_pos  = (self.origin_location.start_pos +
                              self.base_offset +
                              begin + escapes_to_start),
                end_pos    = (self.origin_location.start_pos +
                              self.base_offset +
                              end + escapes_to_end))

        else:
            loc = Source_Reference(
                lexer      = self.origin_location.lexer,
                start_line = self.origin_location.line_no + (start_line - 1),
                start_col  = (self.origin_location.col_no + self.base_offset
                              if start_line == 1
                              else start_col),
                start_pos  = (self.origin_location.start_pos +
                              self.base_offset +
                              begin),
                end_pos    = (self.origin_location.start_pos +
                              self.base_offset +
                              end))

        return loc

    @abstractmethod
    def file_location(self):
        pass

    @abstractmethod
    def token(self):
        pass
