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

"""Lexer for Markdown TRLC (.trlc.md) files.

Converts a Markdown representation of a TRLC requirements file into a
token stream compatible with the TRLC parser.

Markdown format
---------------
The file structure maps to TRLC constructs as follows:

  # PackageName
      → ``package PackageName``

  import pkg
      → ``import pkg``

  ## Section name
      → ``section "Section name" {``

  <hr>
      → Record separator (closes any open record within the section)

  ### Record heading
      → Starts a record; the heading text becomes the record identifier
        (spaces and non-alphanumeric characters are replaced with ``_``).

  Property table (under the ``###`` heading):

    | Property | Value |
    |----------|-------|
    | type     | Foo   |   ← ``type`` row gives the record type name
    | field    | value |   ← subsequent rows are ``field = value`` assignments

  #### Field heading
      → Starts a free-text / string field whose name is the (lowercased)
        heading identifier.  All content that follows—including any Markdown
        tables—is collected verbatim and emitted as a single STRING token.
        The string field ends when the next heading (``##``/``###``/``####``),
        ``<hr>``, or end-of-file is reached.

Value inference
---------------
Values in the property table are interpreted as follows (in order):

  * ``true`` / ``false`` / ``null``  → KEYWORD token
    * Decimal integer (``42``)         → INTEGER token
  * Decimal number  (``3.14``)       → DECIMAL token
  * Hex integer     (``0x1A``)       → INTEGER token
  * Binary integer  (``0b101``)      → INTEGER token
  * Dot-qualified identifier         → chain of IDENTIFIER + DOT tokens
  * Anything else                    → STRING token
"""

from fractions import Fraction

from trlc.lexer import Token, TRLC_Lexer
from trlc.errors import Location, Message_Handler
from trlc.location_md import MD_Location


class MD_Source_Reference(Location):
    """A Location subclass that carries the source line and caret position
    so Message_Handler can render the same visual caret output as TRLC."""

    def __init__(self, file_name, line_no, col_no, source_line):
        super().__init__(file_name, line_no, col_no)
        self._source_line = source_line

    def context_lines(self):
        # Mirror Source_Reference.context_lines() from trlc/lexer.py:
        # return [source_line_stripped, caret_string]
        col = self.col_no if self.col_no else 1
        stripped = self._source_line.lstrip()
        leading = len(self._source_line) - len(stripped)
        caret_col = max(col - 1 - leading, 0)
        return [stripped, " " * caret_col + "^"]


class MD_Lexer(TRLC_Lexer):
    """Lexer that converts a ``.trlc.md`` file to a TRLC token stream.

    The resulting token stream is compatible with :class:`trlc.parser.Parser`
    when the parser is instantiated with a custom *lexer* argument.

    Usage::

        mh    = Message_Handler()
        lexer = MD_Lexer(mh, "path/to/file.trlc.md")
        # pass lexer to Parser(mh, stab, file_name, ..., lexer=lexer)
    """

    # Boolean / null keywords  (mirrors TRLC_Lexer.KEYWORDS)
    KEYWORDS = frozenset(["true", "false", "null", "#", "##", "import"])

    # Markdown-friendly aliases that map to TRLC block tokens.
    MD_SECTION_START_TOKEN = "C_BRA"
    MD_SECTION_END_TOKEN = "C_KET"

    # ------------------------------------------------------------------ #
    # Character classification (mirrors Lexer_Base / TRLC_Lexer helpers)  #
    # ------------------------------------------------------------------ #

    @staticmethod
    def _is_alpha(c):
        return c.isascii() and c.isalpha()

    @staticmethod
    def _is_numeric(c):
        return c.isascii() and c.isdigit()

    @staticmethod
    def _is_alnum(c):
        return c.isascii() and c.isalnum()

    @staticmethod
    def _is_ident_start(c):
        return c == "_" or (c.isascii() and c.isalpha())

    @staticmethod
    def _is_ident_cont(c):
        return c == "_" or (c.isascii() and c.isalnum())

    @staticmethod
    def _is_hex_digit(c):
        return c in "0123456789abcdefABCDEF"

    # ------------------------------------------------------------------ #
    # Value-token scanning helpers                                         #
    # ------------------------------------------------------------------ #

    @staticmethod
    def _scan_integer(text, start=0):
        """Scan a run of decimal digits (and underscores) from *start*.

        Returns the index one past the last scanned character, or ``-1``
        when no digit is present at *start*.
        """
        i = start
        n = len(text)
        if i >= n or not text[i].isdigit():
            return -1
        while i < n and (text[i].isdigit() or text[i] == "_"):
            i += 1
        return i

    @staticmethod
    def _scan_hex(text, start=2):
        """Scan hex digits from *start* (caller has consumed the ``0x`` prefix).

        Returns the end index or ``-1`` if no valid hex digit at *start*.
        """
        i = start
        n = len(text)
        if i >= n or not MD_Lexer._is_hex_digit(text[i]):
            return -1
        while i < n and (MD_Lexer._is_hex_digit(text[i]) or text[i] == "_"):
            i += 1
        return i

    @staticmethod
    def _scan_binary(text, start=2):
        """Scan binary digits from *start* (caller has consumed the ``0b`` prefix).

        Returns the end index or ``-1`` if no valid binary digit at *start*.
        """
        i = start
        n = len(text)
        if i >= n or text[i] not in "01":
            return -1
        while i < n and (text[i] in "01" or text[i] == "_"):
            i += 1
        return i

    @staticmethod
    def _scan_ident(text, start=0):
        """Scan one identifier segment from *text[start]*.

        Returns the end index or ``-1`` when no identifier can start here.
        """
        i = start
        n = len(text)
        if i >= n or not MD_Lexer._is_ident_start(text[i]):
            return -1
        i += 1
        while i < n and MD_Lexer._is_ident_cont(text[i]):
            i += 1
        return i

    # ------------------------------------------------------------------ #
    # Heading / structural helpers                                         #
    # ------------------------------------------------------------------ #

    @staticmethod
    def _parse_heading(line):
        """Return ``(level, content)`` for a Markdown heading, or ``(0, None)``.

        *level* is the number of leading ``#`` characters; *content* is the
        stripped heading text.  Levels 1–4 are meaningful to this lexer.
        """
        i = 0
        while i < len(line) and line[i] == "#":
            i += 1
        if i == 0 or i >= len(line) or not line[i].isspace():
            return 0, None
        content = line[i:].strip()
        if not content:
            return 0, None
        return i, content

    @staticmethod
    def _is_hr(stripped):
        """Return True if *stripped* is a markdown record separator line.

        Accepts ``<hr>``, ``<hr/>``, ``<br>``, ``<br/>`` combinations used in
        exported markdown such as ``<hr><br><hr>``.
        """
        lower = stripped.lower().replace(" ", "")
        if not lower:
            return False

        idx = 0
        saw_hr = False
        while idx < len(lower):
            if lower.startswith("<hr>", idx):
                idx += 4
                saw_hr = True
            elif lower.startswith("<hr/>", idx):
                idx += 5
                saw_hr = True
            elif lower.startswith("<br>", idx):
                idx += 4
            elif lower.startswith("<br/>", idx):
                idx += 5
            else:
                return False

        return saw_hr

    # ------------------------------------------------------------------ #
    # Construction                                                         #
    # ------------------------------------------------------------------ #

    def __init__(self, mh, file_name, file_content=None):
        assert isinstance(mh, Message_Handler)
        assert isinstance(file_name, str)

        self.file_name = file_name

        if file_content is None:
            with open(file_name, "r", encoding="UTF-8") as fd:
                content = fd.read()
        else:
            assert isinstance(file_content, str)
            content = file_content

        # Initialise TRLC_Lexer to satisfy Parser lexer type checks.
        super().__init__(mh, file_name, "")

        self._md_tokens = []  # pre-computed token list
        self._tok_index = 0

        self._process(content)
        # Keep parity with TRLC lexer API expected by linting/reporting.
        self.tokens = self._md_tokens

    # ------------------------------------------------------------------ #
    # Lexer_Base interface                                                 #
    # ------------------------------------------------------------------ #

    def file_location(self):
        return Location(self.file_name, 1, 1)

    def token(self):
        if self._tok_index < len(self._md_tokens):
            tok = self._md_tokens[self._tok_index]
            self._tok_index += 1
            # print("MD_Lexer: end of token stream reached", tok)
            return tok
        return None

    # ------------------------------------------------------------------ #
    # Internal helpers                                                     #
    # ------------------------------------------------------------------ #

    def _loc(self, line_no, col_no=1):
        return Location(self.file_name, line_no, col_no)

    def _source_ref(self, line_no, col_no, source_line):
        """Return a location that renders a caret line, like TRLC Source_Reference."""
        return MD_Source_Reference(self.file_name, line_no, col_no, source_line)

    def _emit(self, location, kind, value=None):
        if kind == "STRING" and not hasattr(location, "text"):
            location = MD_Location(
                file_name=location.file_name,
                line_no=location.line_no,
                col_no=location.col_no,
                token_text=value,
                mh=self.mh,
            )
        self._md_tokens.append(Token(location, kind, value))

    @staticmethod
    def _heading_to_identifier(text):
        """Convert arbitrary heading text to a valid TRLC identifier.

        Replaces any run of non-alphanumeric characters with a single
        underscore and strips leading/trailing underscores.
        """
        result = []
        in_sep = False
        for c in text.strip():
            if c.isascii() and c.isalnum():
                result.append(c)
                in_sep = False
            else:
                if not in_sep:
                    result.append("_")
                    in_sep = True
        return "".join(result).strip("_")

    @staticmethod
    def _is_valid_identifier(name):
        """Return True when *name* matches TRLC identifier syntax."""
        if not name:
            return False
        if not MD_Lexer._is_alpha(name[0]):
            return False
        return all(MD_Lexer._is_alnum(ch) or ch == "_" for ch in name[1:])

    def _validate_identifier(self, name, loc_line, heading_prefix_len, source_line=""):
        """Validate name against TRLC identifier rules.

        Raises lex_error pointing at the first offending character,
        with the same caret-line visual as TRLC's 'unexpected character X'.
        """
        if not name:
            self.mh.lex_error(
                self._source_ref(loc_line, heading_prefix_len + 1, source_line),
                "expected identifier",
            )
        if not MD_Lexer._is_alpha(name[0]):
            self.mh.lex_error(
                self._source_ref(loc_line, heading_prefix_len + 1, source_line),
                "unexpected character '%s'" % name[0],
            )
        for i, ch in enumerate(name[1:], 1):
            if not (MD_Lexer._is_alnum(ch) or ch == "_"):
                self.mh.lex_error(
                    self._source_ref(loc_line, heading_prefix_len + 1 + i, source_line),
                    "unexpected character '%s'" % ch,
                )

    @staticmethod
    def _is_separator_row(row):
        """Return True if *row* is a Markdown table separator (``|---|``)."""
        stripped = row.strip()
        if not stripped.startswith("|"):
            return False
        for c in stripped:
            if c not in "|-: ":
                return False
        return True

    @staticmethod
    def _parse_table_row(row):
        """Split a ``| key | value |`` row into (key, value) strings.

        Returns ``None`` when the row cannot be parsed as a two-column
        table entry.
        """
        stripped = row.strip()
        if not stripped.startswith("|"):
            return None
        # Split on "|", ignore the empty strings at both ends
        parts = [p.strip() for p in stripped.split("|")]
        # After split: ["", cell0, cell1, ..., ""]
        cells = parts[1:-1]
        if len(cells) >= 2:
            return cells[0], cells[1]
        return None

    def _emit_qualified_identifier(self, location, value):
        """Emit IDENTIFIER[/DOT/IDENTIFIER...] tokens for a type name."""
        parts = [p for p in value.split(".") if p]
        for idx, part in enumerate(parts):
            self._emit(location, "IDENTIFIER", part)
            if idx < len(parts) - 1:
                self._emit(location, "DOT")

    def _emit_value(self, raw_value, location):
        """Emit one or more tokens representing a property value.

        Inference rules are applied in the order documented in the
        module docstring.
        """
        value = raw_value.strip()

        # Boolean / null keywords
        if value in MD_Lexer.KEYWORDS:
            self._emit(location, "KEYWORD", value)
            return

        # Positive integers
        end = MD_Lexer._scan_integer(value)
        if end == len(value) and end > 0:
            self._emit(location, "INTEGER", int(value.replace("_", "")))
            return

        # Positive decimals
        dot_pos = value.find(".")
        if dot_pos > 0:
            int_end = MD_Lexer._scan_integer(value, 0)
            if int_end == dot_pos:
                dec_end = MD_Lexer._scan_integer(value, dot_pos + 1)
                if dec_end == len(value) and dec_end > dot_pos + 1:
                    self._emit(location, "DECIMAL", Fraction(value.replace("_", "")))
                    return

        # Hexadecimal  0x…
        if value.startswith("0x") and len(value) > 2:
            end = MD_Lexer._scan_hex(value)
            if end == len(value):
                self._emit(location, "INTEGER", int(value.replace("_", ""), 16))
                return

        # Binary  0b…
        if value.startswith("0b") and len(value) > 2:
            end = MD_Lexer._scan_binary(value)
            if end == len(value):
                self._emit(location, "INTEGER", int(value[2:].replace("_", ""), 2))
                return

        # Dot-qualified identifier or plain identifier
        if value and MD_Lexer._is_ident_start(value[0]):
            parts = []
            i = 0
            valid = True
            while i <= len(value):
                end = MD_Lexer._scan_ident(value, i)
                if end < 0:
                    valid = False
                    break
                parts.append(value[i:end])
                i = end
                if i == len(value):
                    break
                if value[i] == ".":
                    i += 1
                else:
                    valid = False
                    break
            if valid and parts:
                for idx, part in enumerate(parts):
                    self._emit(location, "IDENTIFIER", part)
                    if idx < len(parts) - 1:
                        self._emit(location, "DOT")
                return

        # Fall-back: treat the value as a plain string
        self._emit(location, "STRING", value)

    @staticmethod
    def _looks_like_scalar_value(value):
        """Return True when *value* should be inferred via _emit_value.

        This is used for single-line ``####`` field bodies so short scalar
        values (e.g. enum members, booleans, numbers) behave like table
        properties, while free text remains a STRING.
        """
        text = value.strip()
        if not text:
            return False

        if text in ("true", "false", "null"):
            return True

        # Integer / decimal
        end = MD_Lexer._scan_integer(text)
        if end == len(text) and end > 0:
            return True

        dot_pos = text.find(".")
        if dot_pos > 0:
            int_end = MD_Lexer._scan_integer(text, 0)
            if int_end == dot_pos:
                dec_end = MD_Lexer._scan_integer(text, dot_pos + 1)
                if dec_end == len(text) and dec_end > dot_pos + 1:
                    return True

        # Dot-qualified identifier (used e.g. for enum values)
        if "." in text and MD_Lexer._is_ident_start(text[0]):
            i = 0
            while i <= len(text):
                end = MD_Lexer._scan_ident(text, i)
                if end < 0:
                    return False
                i = end
                if i == len(text):
                    return True
                if text[i] == ".":
                    i += 1
                else:
                    return False

        return False

    # ------------------------------------------------------------------ #
    # Main processing                                                      #
    # ------------------------------------------------------------------ #

    def _process(self, content):
        """Transform *content* into the ``_md_tokens`` list."""

        lines = content.splitlines()
        total_lines = len(lines)

        # ── Section tracking ─────────────────────────────────────────── #
        in_section = False
        imported_packages = []

        # ── Record tracking ───────────────────────────────────────────── #
        # When a ### heading is seen we buffer the name and then wait for
        # the properties table to discover the record type.
        in_record = False
        pending_name = None  # identifier string for the record
        pending_name_loc = None  # Location of the ### line
        pending_props = []  # [(key, value, line_no)] before "type" row
        record_type_found = False
        props_first_row = False  # True while we should skip the header row

        # ── String-field tracking ─────────────────────────────────────── #
        in_string_field = False
        str_field_name = None
        str_field_loc = None
        str_field_lines = []
        # #### fields seen before the "type" row are buffered here, then
        # emitted inside the record after C_BRA (mirrors pending_props).
        pending_string_fields = []  # [(name, loc, text, emit_as_scalar)]

        # ── Helpers (closures) ────────────────────────────────────────── #

        def flush_string_field():
            nonlocal in_string_field, str_field_name, str_field_lines
            if not in_string_field:
                return
            # Strip leading and trailing blank lines
            while str_field_lines and not str_field_lines[0].strip():
                str_field_lines.pop(0)
            while str_field_lines and not str_field_lines[-1].strip():
                str_field_lines.pop()
            text = "\n".join(str_field_lines)

            emit_as_scalar = ("\n" not in text and
                              MD_Lexer._looks_like_scalar_value(text))

            if in_record:
                # Record already open – emit directly inside the block.
                self._emit(str_field_loc, "IDENTIFIER", str_field_name)
                self._emit(str_field_loc, "ASSIGN")
                if emit_as_scalar:
                    self._emit_value(text, str_field_loc)
                else:
                    self._emit(str_field_loc, "STRING", text)
            else:
                # "type" row not yet seen – buffer until the record opens.
                pending_string_fields.append(
                    (str_field_name, str_field_loc, text, emit_as_scalar))
            in_string_field = False
            str_field_name = None
            str_field_lines = []

        def flush_record(loc):
            nonlocal in_record, pending_name, pending_props
            nonlocal record_type_found, props_first_row
            if not in_record:
                # Nothing open – check for incomplete pending record
                if pending_name is not None and not record_type_found:
                    self.mh.error(
                        pending_name_loc,
                        "record heading '%s' has no 'type' property in its "
                        "property table; record will be skipped" % pending_name,
                        fatal=False,
                    )
                pending_name = None
                pending_props = []
                pending_string_fields.clear()
                record_type_found = False
                props_first_row = False
                return
            flush_string_field()
            self._emit(loc, "C_KET")
            in_record = False
            pending_name = None
            pending_props = []
            pending_string_fields.clear()
            record_type_found = False
            props_first_row = False

        def open_section(name, loc):
            nonlocal in_section
            self._emit(loc, "KEYWORD", "##")
            self._emit(loc, "STRING", name)
            self._emit(loc, self.MD_SECTION_START_TOKEN)
            in_section = True

        def close_section(loc):
            nonlocal in_section
            if in_section:
                self._emit(loc, self.MD_SECTION_END_TOKEN)
                in_section = False

        # ── Line-by-line scan ─────────────────────────────────────────── #

        for i, line in enumerate(lines):
            line_no = i + 1
            loc = self._loc(line_no)
            stripped = line.strip()

            # ── While inside a string field, only headings / <hr> break out ─

            if in_string_field:
                level, _ = MD_Lexer._parse_heading(line)
                if level in (2, 3, 4) or MD_Lexer._is_hr(stripped):
                    flush_string_field()
                    # fall through so the line is processed normally
                elif not in_record and stripped.startswith("|"):
                    # A property table row arrived while collecting a ####
                    # string field but before "type" is known.  Close the
                    # string field (buffering its content) so the table row
                    # is processed normally below.
                    flush_string_field()
                    # fall through to table-row handling
                else:
                    str_field_lines.append(line)
                    continue

            # ── Heading dispatch (H1–H4) ─────────────────────────────────

            _h_level, _h_content = MD_Lexer._parse_heading(line)

            # ── H1: package declaration ──────────────────────────────────

            if _h_level == 1:
                parts = _h_content.split()
                if len(parts) != 1:
                    self.mh.lex_error(loc, "package heading must be '# <PackageName>'")
                package_name = parts[0]
                if (
                    not package_name or
                    not MD_Lexer._is_alpha(package_name[0]) or
                    any(not (MD_Lexer._is_alnum(ch) or ch == "_")
                        for ch in package_name[1:])
                ):
                    self.mh.lex_error(loc, "invalid package name in markdown heading")
                self._emit(loc, "KEYWORD", "#")
                self._emit(loc, "IDENTIFIER", package_name)
                continue

            # ── H2: section ──────────────────────────────────────────────
            # _parse_heading already distinguishes the levels by exact count
            # of leading "#" characters, so no prefix-collision is possible.

            if _h_level == 2:
                flush_record(loc)
                close_section(loc)
                open_section(_h_content, loc)
                continue

            # ── H3: record heading ───────────────────────────────────────

            if _h_level == 3:
                flush_record(loc)
                pending_name = _h_content.strip()
                # heading_prefix_len = level(3) + 1 space
                self._validate_identifier(pending_name, line_no, _h_level + 1, line)
                pending_name_loc = loc
                pending_props = []
                record_type_found = False
                props_first_row = True  # skip the column-header row
                continue

            # ── H4: string field heading ─────────────────────────────────

            if _h_level == 4:
                # flush_string_field already called at the top of the loop
                str_field_name = _h_content.strip()
                # heading_prefix_len = level(4) + 1 space
                self._validate_identifier(str_field_name, line_no, _h_level + 1, line)
                str_field_loc = loc
                str_field_lines = []
                in_string_field = True
                continue

            # ── Horizontal rule ──────────────────────────────────────────

            if MD_Lexer._is_hr(stripped):
                flush_record(loc)
                continue

            # ── Table rows ───────────────────────────────────────────────

            if stripped.startswith("|") and pending_name is not None:
                # Skip the column-header row (first row after ###)
                if props_first_row:
                    props_first_row = False
                    continue

                # Skip Markdown separator rows (|---|---|)
                if self._is_separator_row(stripped):
                    continue

                row = self._parse_table_row(stripped)
                if row is None:
                    continue
                key, value = row
                if not key:
                    continue

                if key == "type":
                    # Emit:  RecordType  RecordName  {
                    type_name = value.strip()
                    if "." not in type_name and len(imported_packages) == 1:
                        type_name = imported_packages[0] + "." + type_name
                    self._emit_qualified_identifier(pending_name_loc, type_name)
                    self._emit(pending_name_loc, "IDENTIFIER", pending_name)
                    self._emit(pending_name_loc, "C_BRA")
                    in_record = True
                    record_type_found = True

                    # Flush any properties that arrived before "type"
                    for bkey, bval, bline in pending_props:
                        bloc = self._loc(bline)
                        self._emit(bloc, "IDENTIFIER", bkey)
                        self._emit(bloc, "ASSIGN")
                        self._emit_value(bval, bloc)
                    pending_props = []

                    # Flush any #### string fields that arrived before "type"
                    for fname, floc, ftext, fis_scalar in pending_string_fields:
                        self._emit(floc, "IDENTIFIER", fname)
                        self._emit(floc, "ASSIGN")
                        if fis_scalar:
                            self._emit_value(ftext, floc)
                        else:
                            self._emit(floc, "STRING", ftext)
                    pending_string_fields.clear()

                elif record_type_found:
                    self._emit(loc, "IDENTIFIER", key)
                    self._emit(loc, "ASSIGN")
                    self._emit_value(value, loc)

                else:
                    # Buffer: "type" has not appeared yet
                    pending_props.append((key, value, line_no))

                continue

            # ── Import statement ─────────────────────────────────────────

            if stripped.startswith("import "):
                parts = stripped.split()
                if len(parts) == 2:
                    self._emit(loc, "KEYWORD", "import")
                    self._emit(loc, "IDENTIFIER", parts[1])
                    imported_packages.append(parts[1])
                    continue

            # ── Everything else: delegate to TRLC_Lexer ──────────────────
            # Tokenize the raw line so the parser receives real tokens and
            # can report a meaningful error (e.g. "expected keyword #,
            # encountered OPERATOR instead" for "* foo", or "encountered
            # IDENTIFIER instead" for "sadsad foo").
            if stripped:
                trlc_lex = TRLC_Lexer(self.mh, self.file_name, line)
                tok = trlc_lex.token()
                while tok is not None:
                    self._emit(
                        self._loc(line_no, tok.location.col_no),
                        tok.kind,
                        tok.value,
                    )
                    tok = trlc_lex.token()

        # ── End-of-file cleanup ──────────────────────────────────────────

        eof_loc = self._loc(total_lines + 1)
        flush_record(eof_loc)
        close_section(eof_loc)
