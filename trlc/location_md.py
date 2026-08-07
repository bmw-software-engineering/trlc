#!/usr/bin/env python3
#
# TRLC - Treat Requirements Like Code
# Copyright (C) 2026 Bayerische Motoren Werke Aktiengesellschaft (BMW AG)
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

"""Location helpers used by the Markdown lexer."""

from trlc.errors import Location
from trlc.lexer import TRLC_Lexer


class MD_Location(Location):
    """Location for markdown-emitted STRING tokens.

    Carries the raw string value and exposes ``text()`` so nested lexers can
    treat markdown strings like regular TRLC string literals.
    """

    def __init__(
        self,
        file_name,
        line_no,
        col_no,
        token_text="",
        mh=None,
    ):
        super().__init__(file_name, line_no, col_no)
        self._token_text = token_text
        self._full_text = f'"""{self._token_text}"""'

        # Nested_Lexer.source_location() expects these Source_Reference-like
        # attributes to exist on string literal locations.
        if mh is not None:
            self.lexer = TRLC_Lexer(mh, file_name, self._full_text)
            self.start_pos = 0
            self.end_pos = len(self._full_text) - 1

    def text(self):
        return self._full_text
