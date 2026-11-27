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

  The package heading and the import lines are the markdown spelling of
  the TRLC preamble, so they follow the ``package_name`` and
  ``import_clause`` grammar of the language: the name may be a nested
  package name (``# ns.app``, ``import ns.base``) and an import may be a
  wildcard (``import ns.*``).

  ## Record heading
      → Starts a record; the heading text becomes the record identifier
        (spaces and non-alphanumeric characters are replaced with ``_``).

  Property table (under the ``##`` heading):

    | Property | Value |
    |----------|-------|
    | type     | Foo   |   ← ``type`` row gives the record type name
    | field    | value |   ← subsequent rows are ``field = value`` assignments

  ### Field heading
      → Starts a free-text / string field whose name is the (lowercased)
        heading identifier.  All content that follows—including any Markdown
        tables—is collected verbatim and emitted as a single STRING token.
        The string field ends when the next heading (``##``/``###``),
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

import re
from fractions import Fraction

from trlc import ast as trlc_ast
from trlc.errors import Location, Message_Handler
from trlc.lexer import Token, TRLC_Lexer
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
    KEYWORDS = frozenset(["true", "false", "null", "#", "import"])

    # Matches a genuine HTML line-break tag (``<br>``, ``<br/>``, ``<BR>``,
    # ``<Br  >``, ...). Used to recognize break tags as separators without
    # also treating arbitrary ``<...>`` text the same way.
    _BREAK_TAG_RE = re.compile(r"<[Bb][Rr]\s*/?>")

    # Matches a ``<br>`` tag that sits directly between the ``import``
    # keyword and the package name (e.g. ``import <br> base``). The ``<br>``
    # separator feature is only valid *between or after* complete import
    # clauses, never inside one, so this pattern is used to reject it.
    _LEADING_BREAK_AFTER_IMPORT_RE = re.compile(r"\bimport\b\s*(<[Bb][Rr]\s*/?>)")

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
    def _blank_out_break_tags(line):
        """Replace real ``<br>`` tags with spaces of the same length.

        This keeps column offsets stable while treating a break tag as
        whitespace for tokenization, without silently accepting arbitrary
        ``<...>`` text as a separator.
        """
        return MD_Lexer._BREAK_TAG_RE.sub(lambda m: " " * len(m.group(0)), line)

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

        self._raw_content = content  # kept for Phase 2 reprocessing
        self._stab = None  # set by prepare_phase2() after RSL
        self._md_tokens = []
        self._tok_index = 0

        # Phase 1: emit only preamble tokens (# PackageName, import lines).
        # Phase 2 is triggered by Source_Manager after parse_rsl_files().
        self._process_preamble(content)
        self._preamble_end_index = len(self._md_tokens)
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

    def _process_preamble(self, content):
        """Phase 1: emit only preamble tokens (# PackageName, import lines).

        Body processing is deferred to prepare_phase2() so that RSL types
        are available when field values are tokenised.
        """
        lines = content.splitlines()
        preamble = []
        for line in lines:
            stripped = line.strip()
            if not stripped:
                preamble.append(line)
                continue
            if stripped.startswith("# ") or stripped == "#":
                preamble.append(line)
                continue
            if stripped.startswith("import "):
                preamble.append(line)
                continue
            break  # first non-preamble line stops Phase 1
        self._process("\n".join(preamble))

    def prepare_phase2(self, stab):
        """Phase 2: reprocess the full content with RSL types available.

        Called by Source_Manager after parse_rsl_files() so the stab is
        fully populated.  After this returns, the caller must re-prime the
        parser token cursor (set ct=None and call advance() once).
        """
        self._stab = stab
        self._md_tokens = []
        self._tok_index = 0
        self._process(self._raw_content)  # full reprocessing with types
        self._tok_index = self._preamble_end_index  # skip preamble
        self.tokens = self._md_tokens

    def _resolve_record_type(self, type_name, package_name=None):
        """Look up the Record_Type AST node in the stab for *type_name*."""
        if self._stab is None or not type_name:
            return None
        if "." in type_name:
            # The package part may itself be dotted (nested packages), so
            # only the last segment is the type name.
            pkg_name, local_name = type_name.rsplit(".", 1)
        elif package_name:
            pkg_name, local_name = package_name, type_name
        else:
            return None
        pkg_simple = trlc_ast.Symbol_Table.simplified_name(pkg_name)
        pkg = self._stab.table.get(pkg_simple)
        if not isinstance(pkg, trlc_ast.Package):
            return None
        type_simple = trlc_ast.Symbol_Table.simplified_name(local_name)
        record_type = pkg.symbols.table.get(type_simple)
        if isinstance(record_type, trlc_ast.Record_Type):
            return record_type
        return None

    @staticmethod
    def _get_field_type(record_type_ast, field_name):
        """Return the declared type of *field_name*, or None."""
        if record_type_ast is None:
            return None
        simple = trlc_ast.Symbol_Table.simplified_name(field_name)
        component = record_type_ast.components.table.get(simple)
        return component.n_typ if component is not None else None

    @staticmethod
    def _is_tuple_array_field(field_type):
        """Return True when *field_type* is declared as an array of tuples."""
        return isinstance(field_type, trlc_ast.Array_Type) and isinstance(
            field_type.element_type, trlc_ast.Tuple_Type
        )

    @staticmethod
    def _integer_tuple_arity_of(tuple_type):
        """Return the arity of *tuple_type* if it is a separator-form tuple
        of all-``Integer`` components, or None otherwise.

        Used to recognise the numeric tuple-array shape handled by
        :meth:`_maybe_emit_integer_tuple_array` /
        :meth:`_looks_like_integer_tuple_array` (e.g. ``1234 @ 25``), as
        opposed to a generic tuple-reference array.
        """
        components = list(tuple_type.components.table.values())
        if not tuple_type.has_separators() or not components:
            return None
        if not all(
            isinstance(component.n_typ, trlc_ast.Builtin_Integer)
            for component in components
        ):
            return None
        return len(components)

    @staticmethod
    def _is_string_field(field_type):
        """Return True when *field_type* is a plain String."""
        return isinstance(field_type, trlc_ast.Builtin_String)

    @staticmethod
    def _plain_array_element_type(field_type):
        """Return the element type of a non-tuple array type, or None.

        Used for arrays such as ``Integer [1 .. *]``, ``String [1 .. *]``,
        a plain record-reference array, or an enum array -- i.e. any array
        type whose element type is *not* a tuple (those are handled by
        ``_is_tuple_array_field`` instead).
        """
        if isinstance(field_type, trlc_ast.Array_Type) and not isinstance(
            field_type.element_type, trlc_ast.Tuple_Type
        ):
            return field_type.element_type
        return None

    def _emit_field_value(
        self, raw_value, location, record_type_ast=None, field_name=None
    ):
        """Type-aware field value emission (used in Phase 2).

        Dispatch rules when RSL type info is available:
        - String field       → emit STRING directly (never try array/tuple)
        - Tuple-array field  → type-confirmed array tokenisation
        - Plain array field  → type-confirmed element-wise tokenisation
        - Any other field    → existing _emit_value() heuristics

        Falls back to _emit_value() heuristics when type is unknown.
        """
        if record_type_ast is not None:
            # Resolved once and threaded through the branches below,
            # instead of each helper re-deriving it via its own
            # (record_type_ast, field_name) lookup.
            field_type = self._get_field_type(record_type_ast, field_name)
            if self._is_string_field(field_type):
                self._emit(location, "STRING", raw_value.strip())
                return
            if self._is_tuple_array_field(field_type):
                integer_tuple_arity = self._integer_tuple_arity_of(
                    field_type.element_type
                )
                if self._check_bracket_array(raw_value, location, integer_tuple_arity):
                    return
                if integer_tuple_arity is not None:
                    if self._maybe_emit_integer_tuple_array(
                        raw_value, location, integer_tuple_arity
                    ):
                        return
                    self._report_invalid_array_entry(
                        raw_value,
                        location,
                        field_name,
                        integer_tuple_arity,
                    )
                    return
                if not self._maybe_emit_array(
                    raw_value, location, allow_unqualified=True
                ):
                    self._report_invalid_array_entry(raw_value, location, field_name)
                return
            plain_element_type = self._plain_array_element_type(field_type)
            if plain_element_type is not None:
                if self._check_bracket_array_plain(raw_value, location, field_type):
                    return
                if not self._split_array_elements(raw_value) and (
                    field_type.lower_bound == 0
                ):
                    # The field is simply left blank and the array is
                    # allowed to be empty (lower bound 0) -- this is a
                    # valid empty array, not a missing/invalid value.
                    self._emit(location, "S_BRA")
                    self._emit(location, "S_KET")
                    return
                if not self._maybe_emit_plain_array(
                    raw_value, location, plain_element_type
                ):
                    self._report_invalid_plain_array_entry(
                        raw_value,
                        location,
                        field_type,
                        field_name,
                        plain_element_type,
                    )
                return
        self._emit_value(raw_value, location)

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

    @staticmethod
    def _skip_spaces(line, start):
        """Return the 0-based offset of the first non-whitespace character
        in *line* at or after *start*, so callers can locate a token
        positionally instead of via a substring search that could match an
        earlier, unrelated occurrence."""
        rest = line[start:]
        return start + (len(rest) - len(rest.lstrip()))

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
                f"unexpected character '{name[0]}'",
            )
        for i, ch in enumerate(name[1:], 1):
            if not (MD_Lexer._is_alnum(ch) or ch == "_"):
                self.mh.lex_error(
                    self._source_ref(loc_line, heading_prefix_len + 1 + i, source_line),
                    f"unexpected character '{ch}'",
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

    def _emit_package_name(
        self, name, line_no, name_offset, source_line, allow_wildcard=False
    ):
        """Emit the token stream for a (possibly nested) package name.

        Emits ``IDENTIFIER { DOT IDENTIFIER } [ DOT OPERATOR('*') ]``, i.e.
        exactly what :meth:`trlc.parser.Parser.parse_dotted_name` and
        :meth:`trlc.parser.Parser.parse_import_name` expect, so that
        ``.trlc.md`` preambles share the TRLC grammar for package names.

        *name_offset* is the 0-based column of *name* within *source_line*.
        Each emitted token gets its own caret-capable location (rather than
        one shared line-level location), so a parser error on e.g. the
        second segment of ``ns.bad name`` points at that segment.

        :returns: True if a trailing ``.*`` wildcard was emitted
        """
        # lobster-trace: LRM.Nested_Package_Names
        # lobster-trace: LRM.Wildcard_Import
        segments = name.split(".")
        wildcard = allow_wildcard and len(segments) > 1 and segments[-1] == "*"
        if wildcard:
            segments = segments[:-1]

        offset = name_offset
        for idx, segment in enumerate(segments):
            self._validate_identifier(segment, line_no, offset, source_line)
            if idx:
                self._emit(self._source_ref(line_no, offset, source_line), "DOT")
            self._emit(
                self._source_ref(line_no, offset + 1, source_line),
                "IDENTIFIER",
                segment,
            )
            offset += len(segment) + 1

        if wildcard:
            self._emit(self._source_ref(line_no, offset, source_line), "DOT")
            self._emit(
                self._source_ref(line_no, offset + 1, source_line), "OPERATOR", "*"
            )

        return wildcard

    # Separator symbol token kinds (mirrors TRLC_Lexer.PUNCTUATION).
    _SEPARATOR_PUNCTUATION = {"@": "AT", ":": "COLON", ";": "SEMICOLON"}

    @staticmethod
    def _strip_array_link_targets(raw_value):
        """Keep link labels, skipping balanced and escaped destination parentheses."""
        parts = []
        cursor = 0
        pattern = re.compile(r"\[([^\]]+)\]\(")
        while cursor < len(raw_value):
            match = pattern.search(raw_value, cursor)
            if match is None:
                break
            start = match.start()
            end = match.end()
            depth = 1
            while end < len(raw_value) and depth:
                character = raw_value[end]
                if character == "\\":
                    end += 2
                    continue
                if character == "(":
                    depth += 1
                elif character == ")":
                    depth -= 1
                end += 1
            if depth:
                break
            parts.append(raw_value[cursor:start])
            parts.append(match.group(1))
            cursor = end
        parts.append(raw_value[cursor:])
        return "".join(parts)

    @staticmethod
    def _normalize_array_value(raw_value):
        """Normalize array value by converting various separators to comma format.

        Handles:
        - markdown links (``[text](url)`` -> ``text``)
        - <br> tags (converted to newlines, then normalized)
        - Multiple spaces around @, :, ; separators (normalized to single space)
        - Identifier separators (multiple spaces collapsed to single space)
        - Newlines (preserved initially for multiline detection, then normalized)

        Returns normalized string with tuple refs as
        ``"identifier <sep> integer, ..."``.
        """
        normalized = MD_Lexer._strip_array_link_targets(raw_value)
        normalized = MD_Lexer._BREAK_TAG_RE.sub("\n", normalized)

        # Split on newlines and commas, trim each part
        parts = []
        for line in normalized.split("\n"):
            for item in line.split(","):
                trimmed = item.strip()
                if trimmed:
                    parts.append(trimmed)

        # Normalize whitespace around each part:
        # - punctuation separators (@, :, ;) get exactly one space each side
        # - identifier separators: collapse multiple spaces to one
        normalized_parts = []
        for part in parts:
            part = re.sub(r"\s*([@:;])\s*", r" \1 ", part)
            part = re.sub(r" +", " ", part.strip())
            normalized_parts.append(part)

        return ", ".join(normalized_parts)

    # One tuple-reference entry: identifier (optionally package-qualified)
    # with an optional separator and version, e.g. ``Pkg.item @ 1``,
    # ``item @ 1`` or ``item``. The separator is @, :, ; or a plain identifier.
    _ARRAY_REF_RE = re.compile(
        r"(?P<ref>[a-zA-Z_]\w*(?:\.[a-zA-Z_]\w*)*)"
        r"(?:\s+(?P<sep>[@:;]|[a-zA-Z_]\w*)\s*(?P<ver>\d+))?"
    )

    # Chunk patterns for the multi-separator tuple scanner.
    # A numeric chunk: hex, binary, or decimal (integer or float).
    _TUPLE_NUM_RE = re.compile(
        r"0[xX][0-9a-fA-F][0-9a-fA-F_]*"
        r"|0[bB][01][01_]*"
        r"|\d+(?:\.\d+)?"
    )
    # A separator chunk: @, :, ; or a word identifier.
    _TUPLE_SEP_RE = re.compile(r"[@:;]|[a-zA-Z_]\w*")

    @staticmethod
    def _looks_like_array(raw_value, allow_unqualified=False):
        """Check if value looks like tuple-reference array without emitting.

        Expected format (separator may be @, :, ;, or any identifier)::

          identifier[.identifier]* sep integer
          identifier[.identifier]*
          [, identifier[.identifier]* sep integer]*

        Within Markdown requirement docs, a value may also appear wrapped in a
        markdown link, e.g. ``[req@7](doc.md#req)`` or ``[req](doc.md#req)``.
        The link text is parsed as the reference and the URL target is ignored.

        When *allow_unqualified* is True, unqualified same-package references
        (e.g. ``item @ 1`` or ``item``) are also accepted. Only pass True when
        the field type is confirmed as a tuple-reference array.
        """
        normalized = MD_Lexer._normalize_array_value(raw_value)
        parts = [p.strip() for p in normalized.split(",") if p.strip()]
        if not parts:
            return False
        return all(
            MD_Lexer._matches_array_reference(part, allow_unqualified) for part in parts
        )

    @staticmethod
    def _matches_array_reference(part, allow_unqualified=False):
        """Return True when *part* is a reference, optionally versioned."""
        return MD_Lexer._match_array_reference(part, allow_unqualified) is not None

    @staticmethod
    def _match_array_reference(part, allow_unqualified=False):
        """Return the match for one array entry, or None when it is invalid.

        Without *allow_unqualified* (type unknown) an entry must be
        package-qualified and versioned, so that free text is never
        mistaken for a reference.
        """
        match = MD_Lexer._ARRAY_REF_RE.fullmatch(part.strip())
        if match is None:
            return None
        if not allow_unqualified and (
            match.group("sep") is None or "." not in match.group("ref")
        ):
            return None
        return match

    @staticmethod
    def _looks_like_simple_tuple(raw_value, expected_components=None):
        """Check if value looks like a separator-form tuple: num [sep num]+.

        Handles multi-separator patterns like 0x500:12345@6.1 or 1@2:3;4.
        Returns True only when there is at least one separator (bare numbers
        are handled by the scalar integer/decimal paths in _emit_value).
        """
        value = raw_value.strip()
        pos = 0
        n = len(value)

        def skip_ws():
            nonlocal pos
            while pos < n and value[pos] in (" ", "\t"):
                pos += 1

        skip_ws()
        m = MD_Lexer._TUPLE_NUM_RE.match(value, pos)
        if not m:
            return False
        pos = m.end()
        has_sep = False
        component_count = 1
        while pos < n:
            skip_ws()
            if pos >= n:
                break
            m = MD_Lexer._TUPLE_SEP_RE.match(value, pos)
            if not m:
                return False
            pos = m.end()
            has_sep = True
            skip_ws()
            m = MD_Lexer._TUPLE_NUM_RE.match(value, pos)
            if not m:
                return False
            pos = m.end()
            component_count += 1
        return (
            pos == n
            and has_sep
            and (expected_components is None or component_count == expected_components)
        )

    def _maybe_emit_simple_tuple(self, raw_value, location):
        """Try to emit tokens for a separator-form tuple: num [sep num]+.

        Handles multi-separator patterns such as::

          12345@42       →  INTEGER AT INTEGER
          0x500:12345@6.1 → INTEGER COLON INTEGER AT DECIMAL
          1@2:3;4        →  INTEGER AT INTEGER COLON INTEGER SEMICOLON INTEGER

        Returns True if at least one separator was found and all tokens were
        emitted, False to let _emit_value fall through to STRING.
        """
        value = raw_value.strip()
        pos = 0
        n = len(value)
        chunks = []  # list of ('num', text) | ('sep', text)

        def skip_ws():
            nonlocal pos
            while pos < n and value[pos] in (" ", "\t"):
                pos += 1

        skip_ws()
        m = MD_Lexer._TUPLE_NUM_RE.match(value, pos)
        if not m:
            return False
        chunks.append(("num", m.group()))
        pos = m.end()

        while pos < n:
            skip_ws()
            if pos >= n:
                break
            m = MD_Lexer._TUPLE_SEP_RE.match(value, pos)
            if not m:
                return False
            chunks.append(("sep", m.group()))
            pos = m.end()
            skip_ws()
            m = MD_Lexer._TUPLE_NUM_RE.match(value, pos)
            if not m:
                return False
            chunks.append(("num", m.group()))
            pos = m.end()

        if pos != n:
            return False

        # Must have at least one separator so bare numbers fall through to
        # the integer/decimal scalar checks in _emit_value.
        has_sep = any(kind == "sep" for kind, _ in chunks)
        if not has_sep:
            return False

        for kind, text in chunks:
            if kind == "num":
                if "." in text:
                    self._emit(location, "DECIMAL", Fraction(text.replace("_", "")))
                else:
                    self._emit(location, "INTEGER", self._parse_number(text))
            else:  # sep
                sep_kind = MD_Lexer._SEPARATOR_PUNCTUATION.get(text, "IDENTIFIER")
                sep_val = text if sep_kind == "IDENTIFIER" else None
                self._emit(location, sep_kind, sep_val)

        return True

    def _maybe_emit_parentheses_tuple(self, raw_value, location):
        """Try to emit tokens for a tuple in parentheses form: (val1, val2, val3).

        Returns True if a tuple was emitted, False for fallback to STRING.
        """
        value = raw_value.strip()
        if not (value.startswith("(") and value.endswith(")")):
            return False

        inner = value[1:-1].strip()
        if not inner:
            # Empty tuple () - treat as error or skip
            return False

        # Split by commas and parse each value
        self._emit(location, "BRA")

        parts = [p.strip() for p in inner.split(",") if p.strip()]
        for idx, part in enumerate(parts):
            if idx > 0:
                self._emit(location, "COMMA")

            # Try to infer the value type for each part
            self._emit_value(part, location)

        self._emit(location, "KET")
        return True

    @staticmethod
    def _parse_number(text):
        """Parse a number string (decimal, hex, or binary).

        Returns the integer value or None if parsing fails.
        """
        try:
            text_clean = text.replace("_", "")
            if text_clean.startswith("0x") or text_clean.startswith("0X"):
                return int(text_clean, 16)
            elif text_clean.startswith("0b") or text_clean.startswith("0B"):
                return int(text_clean, 2)
            else:
                return int(text_clean, 10)
        except ValueError:
            return None

    def _check_bracket_array(self, raw_value, location, integer_tuple_arity=None):
        """Detect bracket notation for tuple arrays and emit a clear error.

        Bracket syntax like ``[Pkg.item @ 1, Pkg.item @ 2]`` is not supported
        because brackets conflict with Markdown URL syntax.

        Note: unlike :meth:`_check_bracket_array_plain`, this does not emit a
        recovery array after the error -- the existing system test
        ``tests-system/markdown-array-bracket-error`` (predating this
        change, owned by another contributor) already pins the current
        "no tokens emitted" behavior and its resulting parser cascade, so
        that is intentionally left as-is here rather than changed as a
        side effect of unrelated work.

        Returns True when bracket array syntax was detected (error was emitted),
        so the caller can skip further processing of this value.
        """
        value = raw_value.strip()
        if not (value.startswith("[") and value.endswith("]")):
            return False
        inner = value[1:-1].strip()
        # Only reject if the content inside the brackets actually looks like
        # tuple references – avoids false positives on URLs containing '@'
        if not MD_Lexer._looks_like_array(inner) and not (
            integer_tuple_arity is not None
            and MD_Lexer._looks_like_integer_tuple_array(inner, integer_tuple_arity)
        ):
            return False
        self.mh.error(
            location,
            "bracket notation for tuple-reference arrays is not supported",
            explanation=(
                "Use comma-separated or newline-separated tuple references "
                "without brackets instead, e.g. "
                "'Pkg.item_a @ 1, Pkg.item_b @ 2'"
            ),
            fatal=False,
        )
        return True

    @staticmethod
    def _looks_like_integer_tuple_array(raw_value, expected_components):
        normalized = MD_Lexer._normalize_array_value(raw_value)
        parts = [part.strip() for part in normalized.split(",") if part.strip()]
        return bool(parts) and all(
            MD_Lexer._looks_like_simple_tuple(part, expected_components)
            for part in parts
        )

    def _maybe_emit_integer_tuple_array(self, raw_value, location, expected_components):
        normalized = MD_Lexer._normalize_array_value(raw_value)
        parts = [part.strip() for part in normalized.split(",") if part.strip()]
        if not parts or not all(
            MD_Lexer._looks_like_simple_tuple(part, expected_components)
            for part in parts
        ):
            return False

        self._emit(location, "S_BRA")
        for idx, part in enumerate(parts):
            if idx:
                self._emit(location, "COMMA")
            self._maybe_emit_simple_tuple(part, location)
        self._emit(location, "S_KET")
        return True

    def _maybe_emit_array(self, raw_value, location, allow_unqualified=False):
        """Try to emit array tokens for tuple-reference format.

        When *allow_unqualified* is True, unqualified same-package references
        (e.g. ``item @ 1`` or ``item``) are also accepted. Only safe when the
        field type is confirmed as a tuple-reference array (Phase 2 path).

        Recognises values of the form::

          Package.item sep integer [, Package.item sep integer]*
          item [sep integer]

        Returns True if array was emitted, False for STRING fallback.
        """
        if not self._looks_like_array(raw_value, allow_unqualified=allow_unqualified):
            return False

        normalized = self._normalize_array_value(raw_value)
        parts = [p.strip() for p in normalized.split(",")]
        self._emit(location, "S_BRA")

        for idx, part in enumerate(parts):
            if idx > 0:
                self._emit(location, "COMMA")

            # _looks_like_array() has validated every entry already.
            match = MD_Lexer._match_array_reference(part, allow_unqualified)
            ident_parts = match.group("ref").split(".")
            for i, ident_part in enumerate(ident_parts):
                self._emit(location, "IDENTIFIER", ident_part)
                if i < len(ident_parts) - 1:
                    self._emit(location, "DOT")

            sep = match.group("sep")
            if sep is not None:
                sep_kind = MD_Lexer._SEPARATOR_PUNCTUATION.get(sep, "IDENTIFIER")
                sep_val = sep if sep_kind == "IDENTIFIER" else None
                self._emit(location, sep_kind, sep_val)
                self._emit(location, "INTEGER", int(match.group("ver")))

        self._emit(location, "S_KET")
        return True

    def _report_invalid_array_entry(
        self, raw_value, location, field_name, integer_tuple_arity=None
    ):
        """Report the first entry of a tuple-array value that is not a reference.

        Emits an empty array afterwards so the parser does not add a
        misleading follow-up error for the same value.
        """
        normalized = self._normalize_array_value(raw_value)
        parts = [p.strip() for p in normalized.split(",") if p.strip()]
        if integer_tuple_arity is None:
            invalid = next(
                (p for p in parts if self._match_array_reference(p, True) is None),
                raw_value.strip(),
            )
            message = (
                f"invalid entry '{invalid}' in tuple-reference array field "
                f"'{field_name}'"
            )
            explanation = (
                "Use an identifier with an optional version, e.g. 'item' or "
                "'item @ 1'. Identifiers may only contain letters, digits "
                "and underscores."
            )
        else:
            invalid = next(
                (
                    p
                    for p in parts
                    if not self._looks_like_simple_tuple(p, integer_tuple_arity)
                ),
                raw_value.strip(),
            )
            message = (
                f"invalid entry '{invalid}' in integer tuple array field '{field_name}'"
            )
            explanation = (
                "Use integer tuple values with the declared separators, "
                "e.g. '1234 @ 25'."
            )
        self.mh.error(
            location,
            message,
            explanation=explanation,
            fatal=False,
        )
        self._emit(location, "S_BRA")
        self._emit(location, "S_KET")

    # ------------------------------------------------------------------ #
    # Plain (non-tuple) array helpers                                      #
    # ------------------------------------------------------------------ #

    # A plain identifier chain, used for both enum literals
    # (``Pkg.Enum.Literal``) and record references (``Pkg.item`` or, for
    # the same package, just ``item``). No separator/version suffix is
    # accepted here -- that is only valid for tuple elements.
    _PLAIN_ARRAY_IDENT_RE = re.compile(r"[a-zA-Z_]\w*(?:\.[a-zA-Z_]\w*)*")

    # A signed integer literal: decimal, hex, or binary.
    _PLAIN_ARRAY_INT_RE = re.compile(
        r"[+-]?(?:0[xX][0-9a-fA-F][0-9a-fA-F_]*|0[bB][01][01_]*|[0-9][0-9_]*)"
    )

    # A signed decimal literal.
    _PLAIN_ARRAY_DECIMAL_RE = re.compile(r"[+-]?[0-9][0-9_]*\.[0-9][0-9_]*")

    @staticmethod
    def _split_top_level_commas(text):
        """Split *text* on commas, except commas inside a quoted string.

        This keeps a quoted String array element such as ``"a, b"`` intact
        while still splitting ``item_a, item_b`` into two entries. A
        backslash-escaped quote (``\\"``) inside a string does not toggle
        the quoted state, so a string containing an escaped quote followed
        by a comma (e.g. ``"a\\", b"``) is also kept intact rather than
        being mis-split at that comma.
        """
        parts = []
        current = []
        in_string = False
        i = 0
        n = len(text)
        while i < n:
            ch = text[i]
            if in_string and ch == "\\" and i + 1 < n:
                current.append(ch)
                current.append(text[i + 1])
                i += 2
                continue
            if ch == '"':
                in_string = not in_string
                current.append(ch)
            elif ch == "," and not in_string:
                parts.append("".join(current))
                current = []
            else:
                current.append(ch)
            i += 1
        parts.append("".join(current))
        return parts

    @staticmethod
    def _split_array_elements(raw_value):
        """Split a plain-array field value into its individual elements.

        Handles Markdown link labels (``[label](url)`` -> ``label``),
        ``<br>`` tags, and newlines the same way as tuple arrays, then
        splits each resulting line on top-level commas (see
        :meth:`_split_top_level_commas`).
        """
        normalized = MD_Lexer._strip_array_link_targets(raw_value)
        normalized = MD_Lexer._BREAK_TAG_RE.sub("\n", normalized)

        elements = []
        for line in normalized.split("\n"):
            for piece in MD_Lexer._split_top_level_commas(line):
                trimmed = piece.strip()
                if trimmed:
                    elements.append(trimmed)
        return elements

    @staticmethod
    def _unquote_string(text):
        """Strip surrounding double quotes and unescape ``\\"``, if present.

        Elements are also accepted without quotes (consistent with how a
        plain, non-array String field is handled), in which case the text
        is used verbatim.
        """
        if len(text) >= 2 and text.startswith('"') and text.endswith('"'):
            return text[1:-1].replace('\\"', '"')
        return text

    @staticmethod
    def _parse_plain_element(text, element_type):
        """Classify one array element against *element_type*.

        Returns a ``(kind, text)`` pair on success, or ``None`` when *text*
        does not look like a valid value of *element_type*.
        """
        value = text.strip()
        if not value:
            return None

        if isinstance(element_type, trlc_ast.Builtin_Boolean):
            return ("BOOL", value) if value in ("true", "false") else None

        if isinstance(element_type, trlc_ast.Builtin_Integer):
            if MD_Lexer._PLAIN_ARRAY_INT_RE.fullmatch(value):
                return ("INT", value)
            return None

        if isinstance(element_type, trlc_ast.Builtin_Decimal):
            if MD_Lexer._PLAIN_ARRAY_DECIMAL_RE.fullmatch(value):
                return ("DEC", value)
            return None

        if isinstance(element_type, trlc_ast.Builtin_String):
            # Any text is a valid String value (quotes are optional).
            return ("STR", value)

        if isinstance(
            element_type,
            (trlc_ast.Enumeration_Type, trlc_ast.Record_Type, trlc_ast.Union_Type),
        ):
            if MD_Lexer._PLAIN_ARRAY_IDENT_RE.fullmatch(value):
                return ("IDENT", value)
            return None

        return None

    def _emit_plain_element(self, parsed_element, location):
        """Emit the token(s) for one ``(kind, text)`` pair from
        :meth:`_parse_plain_element`."""
        kind, text = parsed_element

        if kind == "BOOL":
            self._emit(location, "KEYWORD", text)
            return

        if kind in ("INT", "DEC"):
            body = text
            sign = None
            if body and body[0] in "+-":
                sign, body = body[0], body[1:]
            if sign:
                self._emit(location, "OPERATOR", sign)
            if kind == "INT":
                self._emit(location, "INTEGER", self._parse_number(body))
            else:
                self._emit(location, "DECIMAL", Fraction(body.replace("_", "")))
            return

        if kind == "STR":
            self._emit(location, "STRING", self._unquote_string(text))
            return

        # kind == "IDENT": enum literal or (qualified/unqualified) record
        # reference -- both are a plain IDENTIFIER/DOT chain.
        self._emit_qualified_identifier(location, text)

    def _maybe_emit_plain_array(self, raw_value, location, element_type):
        """Try to emit array tokens for a non-tuple array field.

        Splits *raw_value* into elements (comma/newline/``<br>``-separated)
        and validates each one against *element_type*. Returns True and
        emits ``S_BRA elem [, elem]* S_KET`` on success, or False (emitting
        nothing) when any element does not match.
        """
        elements = self._split_array_elements(raw_value)
        if not elements:
            return False

        parsed = [self._parse_plain_element(e, element_type) for e in elements]
        if any(p is None for p in parsed):
            return False

        self._emit(location, "S_BRA")
        for idx, parsed_element in enumerate(parsed):
            if idx:
                self._emit(location, "COMMA")
            self._emit_plain_element(parsed_element, location)
        self._emit(location, "S_KET")
        return True

    # Element types whose Type.get_example_value() is guaranteed to
    # resolve/parse on its own -- i.e. it never names another record
    # instance that might not actually exist in the model (unlike e.g.
    # Record_Type.get_example_value(), which fabricates a plausible but
    # unresolved identifier such as "Item_instance").
    _SAFE_EXAMPLE_VALUE_TYPES = (
        trlc_ast.Builtin_Boolean,
        trlc_ast.Builtin_Integer,
        trlc_ast.Builtin_Decimal,
        trlc_ast.Builtin_String,
        trlc_ast.Enumeration_Type,
    )

    def _emit_recovery_array(self, location, array_type_ast):
        """Emit array tokens to recover after a rejected plain-array value
        (bracket notation, an invalid entry, or tuple syntax on a
        plain-ref field).

        When the element type is one of :data:`_SAFE_EXAMPLE_VALUE_TYPES`,
        emit enough placeholder elements (via ``Type.get_example_value()``)
        to satisfy the field's minimum element count. This avoids the
        generic array-length check in the parser also reporting a
        misleading "only 0 provided" cascade for a value that in fact had
        entries -- they were just rejected for a different reason.

        Falls back to an empty array otherwise (e.g. a record/union/tuple
        reference element, whose generated example name might not exist
        in the model): fabricating an unresolved reference there would
        just trade one confusing cascade for another.
        """
        placeholder = None
        count = 0
        if isinstance(array_type_ast, trlc_ast.Array_Type) and isinstance(
            array_type_ast.element_type, MD_Lexer._SAFE_EXAMPLE_VALUE_TYPES
        ):
            element_type = array_type_ast.element_type
            placeholder = self._parse_plain_element(
                element_type.get_example_value(), element_type
            )
            count = array_type_ast.lower_bound if placeholder is not None else 0

        self._emit(location, "S_BRA")
        for idx in range(count):
            if idx:
                self._emit(location, "COMMA")
            self._emit_plain_element(placeholder, location)
        self._emit(location, "S_KET")

    def _check_bracket_array_plain(self, raw_value, location, array_type_ast):
        """Reject bracket notation for a plain (non-tuple) array field.

        Mirrors :meth:`_check_bracket_array`, but the element shape is
        irrelevant here: the field's type is already confirmed to be an
        array, so any bracket-wrapped value is rejected unconditionally.
        """
        value = raw_value.strip()
        if not (value.startswith("[") and value.endswith("]")):
            return False
        self.mh.error(
            location,
            "bracket notation for array fields is not supported",
            explanation=(
                "Use comma-separated or newline-separated values without "
                "brackets instead, e.g. '1, 2, 3'."
            ),
            fatal=False,
        )
        self._emit_recovery_array(location, array_type_ast)
        return True

    _PLAIN_ARRAY_EXAMPLE = {
        trlc_ast.Builtin_Boolean: "true, false",
        trlc_ast.Builtin_Integer: "1, 2, 3",
        trlc_ast.Builtin_Decimal: "1.0, 2.5",
        trlc_ast.Builtin_String: '"foo", "bar"',
    }

    @staticmethod
    def _plain_array_example(element_type):
        """Return a short example value list for *element_type*'s error text."""
        for typ, example in MD_Lexer._PLAIN_ARRAY_EXAMPLE.items():
            if isinstance(element_type, typ):
                return example
        if isinstance(element_type, trlc_ast.Enumeration_Type):
            return f"{element_type.name}.<Literal>"
        return "item_a, item_b"

    def _report_invalid_plain_array_entry(
        self, raw_value, location, array_type_ast, field_name, element_type
    ):
        """Report why a plain-array value could not be parsed: either it
        has no elements at all, or one of its entries does not match the
        declared element type.

        Emits a recovery array afterwards (see :meth:`_emit_recovery_array`)
        so the parser does not add a misleading "only 0 provided" cascade
        for a value that in fact had entries, when a safe placeholder can
        be fabricated for the element type.
        """
        elements = self._split_array_elements(raw_value)
        example = self._plain_array_example(element_type)
        if not elements:
            message = f"array field '{field_name}' has no elements"
            explanation = (
                f"Provide at least one value of type '{element_type.name}', "
                f"separated by commas or newlines, e.g. '{example}'."
            )
        else:
            invalid = next(
                (
                    e
                    for e in elements
                    if self._parse_plain_element(e, element_type) is None
                ),
                raw_value.strip(),
            )
            message = f"invalid entry '{invalid}' in array field '{field_name}'"
            explanation = (
                f"Expected a value of type '{element_type.name}', separated by "
                f"commas or newlines, e.g. '{example}'."
            )
        self.mh.error(
            location,
            message,
            explanation=explanation,
            fatal=False,
        )
        self._emit_recovery_array(location, array_type_ast)

    def _emit_value(self, raw_value, location):
        """Emit one or more tokens representing a property value.

        Inference rules are applied in the order documented in the
        module docstring.
        """
        value = raw_value.strip()

        # Bracket array notation is not supported – emit a clear error
        if self._check_bracket_array(raw_value, location):
            return

        # Parentheses tuple form: (val1, val2, val3)
        if self._maybe_emit_parentheses_tuple(raw_value, location):
            return

        # Array of tuple references (before other checks)
        if self._maybe_emit_array(raw_value, location):
            return

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

        # Simple tuple syntax (e.g., 12345@42, 0x500:6.1)
        if self._maybe_emit_simple_tuple(raw_value, location):
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

        This is used for single-line ``###`` field bodies so short scalar
        values (e.g. enum members, booleans, numbers) behave like table
        properties, while free text remains a STRING.
        """
        text = value.strip()
        if not text:
            return False

        if text in ("true", "false", "null"):
            return True

        # Parentheses tuple form (simple detection)
        if text.startswith("(") and text.endswith(")"):
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

        # Simple tuple syntax (e.g., 12345@42)
        if MD_Lexer._looks_like_simple_tuple(text):
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

        imported_packages = []

        # ── Type tracking for Phase 2 ─────────────────────────────────── #
        current_package_name = None  # from # PackageName heading
        current_record_type_ast = None  # resolved after type row found

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
        str_field_first_content_line = None
        str_field_first_content_col = 1
        # ### fields seen before the "type" row are buffered here, then
        # emitted inside the record after C_BRA (mirrors pending_props).
        # Tuple: (name, loc, text, emit_as_scalar, is_array, is_bracket)
        pending_string_fields = []

        # ── Helpers (closures) ────────────────────────────────────────── #

        def flush_string_field():
            nonlocal in_string_field, str_field_name, str_field_lines
            nonlocal str_field_first_content_line, str_field_first_content_col
            if not in_string_field:
                return
            # Strip leading and trailing blank lines
            while str_field_lines and not str_field_lines[0].strip():
                str_field_lines.pop(0)
            while str_field_lines and not str_field_lines[-1].strip():
                str_field_lines.pop()
            text = "\n".join(str_field_lines)

            emit_as_scalar = "\n" not in text and MD_Lexer._looks_like_scalar_value(
                text
            )

            value_loc = str_field_loc
            if str_field_first_content_line is not None:
                value_loc = self._loc(
                    str_field_first_content_line,
                    str_field_first_content_col,
                )

            if in_record:
                # Record already open – emit directly inside the block.
                self._emit(str_field_loc, "IDENTIFIER", str_field_name)
                self._emit(str_field_loc, "ASSIGN")
                self._emit_field_value(
                    text, value_loc, current_record_type_ast, str_field_name
                )
            else:
                # "type" row not yet seen – buffer until the record opens.
                # Check if it looks like an array (but don't emit yet)
                is_bracket = (
                    not emit_as_scalar
                    and text.strip().startswith("[")
                    and text.strip().endswith("]")
                    and "@" in text
                )
                is_array = (
                    not emit_as_scalar
                    and not is_bracket
                    and MD_Lexer._looks_like_array(text)
                )
                pending_string_fields.append(
                    (
                        str_field_name,
                        value_loc,
                        text,
                        emit_as_scalar,
                        is_array,
                        is_bracket,
                    )
                )
            in_string_field = False
            str_field_name = None
            str_field_lines = []
            str_field_first_content_line = None
            str_field_first_content_col = 1

        def flush_record(loc):
            nonlocal in_record, pending_name, pending_props
            nonlocal record_type_found, props_first_row
            if not in_record:
                # Nothing open – check for incomplete pending record
                if pending_name is not None and not record_type_found:
                    self.mh.error(
                        pending_name_loc,
                        f"record heading '{pending_name}' has no 'type' property"
                        " in its property table; record will be skipped",
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

        # ── Line-by-line scan ─────────────────────────────────────────── #

        for i, line in enumerate(lines):
            line_no = i + 1
            loc = self._loc(line_no)
            stripped = line.strip()

            # ── While inside a string field, only headings / <hr> break out ─

            if in_string_field:
                level, _ = MD_Lexer._parse_heading(line)
                if level in (2, 3) or MD_Lexer._is_hr(stripped):
                    flush_string_field()
                    # fall through so the line is processed normally
                elif not in_record and stripped.startswith("|"):
                    # A property table row arrived while collecting a ###
                    # string field but before "type" is known. Close the
                    # string field (buffering its content) so the table row
                    # is processed normally below.
                    flush_string_field()
                    # fall through to table-row handling
                else:
                    if str_field_first_content_line is None and stripped:
                        line_stripped = line.lstrip()
                        str_field_first_content_line = line_no
                        str_field_first_content_col = len(line) - len(line_stripped) + 1
                    str_field_lines.append(line)
                    continue

            # ── Heading dispatch (H1–H3) ─────────────────────────────────

            _h_level, _h_content = MD_Lexer._parse_heading(line)

            # ── H1: package declaration ──────────────────────────────────

            if _h_level == 1:
                parts = _h_content.split()
                if len(parts) != 1:
                    self.mh.lex_error(loc, "package heading must be '# <PackageName>'")
                package_name = parts[0]
                self._emit(loc, "KEYWORD", "#")
                # Package name starts right after the '#' and its following
                # whitespace; computed positionally so a name that happens
                # to reoccur earlier on the line (e.g. inside "##") can't
                # be found at the wrong offset.
                name_offset = MD_Lexer._skip_spaces(line, _h_level)
                self._emit_package_name(package_name, line_no, name_offset, line)
                current_package_name = package_name
                continue

            # ── H2: record heading ────────────────────────────────────────
            # _parse_heading already distinguishes the levels by exact count
            # of leading "#" characters, so no prefix-collision is possible.

            if _h_level == 2:
                flush_record(loc)
                pending_name = _h_content.strip()
                self._validate_identifier(pending_name, line_no, _h_level + 1, line)
                pending_name_loc = loc
                pending_props = []
                record_type_found = False
                props_first_row = True  # skip the column-header row
                continue

            # ── H3: string field heading ─────────────────────────────────

            if _h_level == 3:
                # flush_string_field already called at the top of the loop
                str_field_name = _h_content.strip()
                self._validate_identifier(str_field_name, line_no, _h_level + 1, line)
                str_field_loc = loc
                str_field_lines = []
                str_field_first_content_line = None
                str_field_first_content_col = 1
                in_string_field = True
                continue

            if _h_level >= 4:
                self.mh.lex_error(
                    loc,
                    "heading level 4 and above is not valid in .trlc.md; use "
                    "'##' for records and '###' for fields",
                )
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
                    self._emit_qualified_identifier(loc, type_name)
                    self._emit(pending_name_loc, "IDENTIFIER", pending_name)
                    self._emit(pending_name_loc, "C_BRA")
                    in_record = True
                    record_type_found = True
                    current_record_type_ast = self._resolve_record_type(
                        type_name, package_name=current_package_name
                    )

                    # Flush any properties that arrived before "type"
                    for bkey, bval, bline in pending_props:
                        bloc = self._loc(bline)
                        self._emit(bloc, "IDENTIFIER", bkey)
                        self._emit(bloc, "ASSIGN")
                        self._emit_field_value(
                            bval, bloc, current_record_type_ast, bkey
                        )
                    pending_props = []

                    # Flush any ### string fields that arrived
                    # before "type"
                    for (
                        fname,
                        floc,
                        ftext,
                        _fis_scalar,
                        _fis_array,
                        _fis_bracket,
                    ) in pending_string_fields:
                        self._emit(floc, "IDENTIFIER", fname)
                        self._emit(floc, "ASSIGN")
                        self._emit_field_value(
                            ftext, floc, current_record_type_ast, fname
                        )
                    pending_string_fields.clear()

                elif record_type_found:
                    self._emit(loc, "IDENTIFIER", key)
                    self._emit(loc, "ASSIGN")
                    self._emit_field_value(value, loc, current_record_type_ast, key)

                else:
                    # Buffer: "type" has not appeared yet
                    pending_props.append((key, value, line_no))

                continue

            # ── Import statement ─────────────────────────────────────────

            if stripped.startswith("import "):
                # A <br> tag is only a valid separator *between* or *after*
                # complete "import <name>" clauses; reject one wedged
                # between the "import" keyword and its package name (e.g.
                # "import <br> base") instead of silently discarding it.
                bad_tag = MD_Lexer._LEADING_BREAK_AFTER_IMPORT_RE.search(line)
                if bad_tag is not None:
                    self.mh.lex_error(
                        self._source_ref(line_no, bad_tag.start(1) + 1, line),
                        "a <br> tag is not allowed between 'import' and the"
                        " package name",
                    )

                # Replace real HTML break tags with spaces so adjacent imports
                # still parse as separate clauses without shifting column
                # offsets; leave arbitrary "<...>" text alone.
                scrubbed = MD_Lexer._blank_out_break_tags(line)
                for match in re.finditer(r"import\s+\S+", scrubbed):
                    import_text = match.group(0)
                    parts = import_text.split()
                    if len(parts) != 2:
                        continue

                    kw_loc = self._loc(line_no, match.start() + 1)
                    self._emit(kw_loc, "KEYWORD", "import")
                    # Compute each package offset from its own match so extra
                    # whitespace after "import" does not skew locations.
                    name_offset = MD_Lexer._skip_spaces(
                        scrubbed, match.start() + len("import")
                    )
                    wildcard = self._emit_package_name(
                        parts[1],
                        line_no,
                        name_offset,
                        line,
                        allow_wildcard=True,
                    )
                    # Only a plain import identifies a single package that
                    # unqualified type names can be completed with.
                    if not wildcard:
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
