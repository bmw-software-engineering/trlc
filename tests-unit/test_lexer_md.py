import unittest
from fractions import Fraction

from trlc import ast as trlc_ast
from trlc.errors import Kind, Location, Message_Handler, TRLC_Error
from trlc.lexer import Token
from trlc.lexer_md import MD_Lexer
from trlc.trlc_markdown_parser import TrlcMarkdownParser


class ListHandler(Message_Handler):
    def __init__(self):
        super().__init__()
        self.messages = []

    def emit(self, location, kind, message, fatal=True, extrainfo=None):
        if not isinstance(location, Location):
            raise TypeError(f"expected Location, got {type(location).__name__}")
        if not isinstance(kind, Kind):
            raise TypeError(f"expected Kind, got {type(kind).__name__}")
        if not isinstance(message, str):
            raise TypeError(f"expected str message, got {type(message).__name__}")
        if not isinstance(fatal, bool):
            raise TypeError(f"expected bool fatal, got {type(fatal).__name__}")
        if extrainfo is not None and not isinstance(extrainfo, str):
            raise TypeError(
                f"expected str or None extrainfo, got {type(extrainfo).__name__}"
            )

        self.messages.append((location, kind, message))

        if fatal:
            raise TRLC_Error(location, kind, message)

    def pop_message(self):
        if not self.messages:
            raise AssertionError("pop_message called with no messages")
        message, self.messages = self.messages[0], self.messages[1:]
        return message


def token_pairs(lexer):
    pairs = []
    while True:
        token = lexer.token()
        if token is None:
            break
        pairs.append((token.kind, token.value))
    return pairs


def all_tokens(lexer):
    tokens = []
    while True:
        token = lexer.token()
        if token is None:
            break
        tokens.append(token)
    return tokens


def make_record_type(record_name="ReqType"):
    builtin_stab = trlc_ast.Symbol_Table()
    package = trlc_ast.Package("DemoPkg", Location("test"), builtin_stab, False)
    record_type = trlc_ast.Record_Type(
        record_name,
        None,
        Location("test"),
        package,
        None,
        False,
    )

    record_type.components.table["notes"] = trlc_ast.Composite_Component(
        "notes",
        None,
        Location("test"),
        record_type,
        trlc_ast.Builtin_String(),
        False,
    )

    tuple_type = trlc_ast.Tuple_Type(
        "TupleType",
        None,
        Location("test"),
        package,
    )
    array_type = trlc_ast.Array_Type(
        Location("test"),
        tuple_type,
        Location("test"),
        0,
        Location("test"),
        None,
    )
    record_type.components.table["refs"] = trlc_ast.Composite_Component(
        "refs",
        None,
        Location("test"),
        record_type,
        array_type,
        False,
    )

    package.symbols.table[trlc_ast.Symbol_Table.simplified_name(record_name)] = (
        record_type
    )

    stab = trlc_ast.Symbol_Table()
    stab.table[trlc_ast.Symbol_Table.simplified_name(package.name)] = package
    return stab, record_type


class TestLexerMd(unittest.TestCase):
    def setUp(self):
        self.mh = ListHandler()

    def tearDown(self):
        self.assertEqual(
            len(self.mh.messages),
            0,
            f"unexpected messages: {', '.join(msg[2] for msg in self.mh.messages)}",
        )

    def test_heading_and_rule_helpers(self):
        self.assertEqual(MD_Lexer._parse_heading("## Record Name"), (2, "Record Name"))
        self.assertEqual(MD_Lexer._parse_heading("### Field Name"), (3, "Field Name"))
        self.assertEqual(MD_Lexer._parse_heading("###"), (0, None))
        self.assertEqual(MD_Lexer._parse_heading("#NotAHeading"), (0, None))
        self.assertEqual(MD_Lexer._parse_heading("#### NotAllowed"), (4, "NotAllowed"))

        self.assertTrue(MD_Lexer._is_hr("<hr>"))
        self.assertTrue(MD_Lexer._is_hr("<hr><br><hr/>"))
        self.assertTrue(MD_Lexer._is_hr("<BR/> <HR>"))
        self.assertFalse(MD_Lexer._is_hr("<hrx>"))

        self.assertEqual(
            MD_Lexer._heading_to_identifier("  Hello, world!  "), "Hello_world"
        )
        self.assertEqual(MD_Lexer._heading_to_identifier("A---B__C"), "A_B_C")

    def test_table_helpers(self):
        self.assertTrue(MD_Lexer._is_separator_row("|---|---|"))
        self.assertTrue(MD_Lexer._is_separator_row("|:---|---:|"))
        self.assertFalse(MD_Lexer._is_separator_row("| value |"))

        self.assertEqual(MD_Lexer._parse_table_row("| key | value |"), ("key", "value"))
        self.assertEqual(
            MD_Lexer._parse_table_row("| key | value | extra |"), ("key", "value")
        )
        self.assertIsNone(MD_Lexer._parse_table_row("not a row"))

    def test_scalar_value_inference(self):
        lexer = MD_Lexer(self.mh, "test", "")

        lexer._emit_value("true", Location("test"))
        lexer._emit_value("42", Location("test"))
        lexer._emit_value("3.25", Location("test"))
        lexer._emit_value("0x10", Location("test"))
        lexer._emit_value("0b11", Location("test"))
        lexer._emit_value("Pkg.Enum.Value", Location("test"))
        lexer._emit_value("(1, false, 2)", Location("test"))
        lexer._emit_value("0x500:12345@6.1", Location("test"))
        lexer._emit_value("plain text", Location("test"))

        self.assertEqual(
            token_pairs(lexer),
            [
                ("KEYWORD", "true"),
                ("INTEGER", 42),
                ("DECIMAL", Fraction("3.25")),
                ("INTEGER", 16),
                ("INTEGER", 3),
                ("IDENTIFIER", "Pkg"),
                ("DOT", None),
                ("IDENTIFIER", "Enum"),
                ("DOT", None),
                ("IDENTIFIER", "Value"),
                ("BRA", None),
                ("INTEGER", 1),
                ("COMMA", None),
                ("KEYWORD", "false"),
                ("COMMA", None),
                ("INTEGER", 2),
                ("KET", None),
                ("INTEGER", 0x500),
                ("COLON", None),
                ("INTEGER", 12345),
                ("AT", None),
                ("DECIMAL", Fraction("6.1")),
                ("STRING", "plain text"),
            ],
        )

    def test_array_value_and_bracket_error(self):
        lexer = MD_Lexer(self.mh, "test", "")
        lexer._emit_value(
            "DemoPkg.item_a @ 1 <br> DemoPkg.item_b via 2", Location("test")
        )
        self.assertEqual(
            token_pairs(lexer),
            [
                ("S_BRA", None),
                ("IDENTIFIER", "DemoPkg"),
                ("DOT", None),
                ("IDENTIFIER", "item_a"),
                ("AT", None),
                ("INTEGER", 1),
                ("COMMA", None),
                ("IDENTIFIER", "DemoPkg"),
                ("DOT", None),
                ("IDENTIFIER", "item_b"),
                ("IDENTIFIER", "via"),
                ("INTEGER", 2),
                ("S_KET", None),
            ],
        )

        lexer = MD_Lexer(self.mh, "test", "")
        lexer._emit_value("[DemoPkg.item_a @ 1, DemoPkg.item_b @ 2]", Location("test"))
        self.assertEqual(token_pairs(lexer), [])
        self.assertEqual(len(self.mh.messages), 1)
        self.assertEqual(
            self.mh.pop_message()[2],
            "bracket notation for tuple-reference arrays is not supported",
        )

    def test_markdown_requirement_reference_array(self):
        _stab, record_type = make_record_type()

        lexer = MD_Lexer(self.mh, "test", "")
        lexer._emit_field_value(
            "[requ1@26](document.md#requ1), requ2@27, requ3@28, "
            "[requ4@29](to-be-ignored.md#whatever), requ5, "
            "[requ6](also-to-be-ignored.md#whatever), "
            "[requ7](some totally unrelated string)",
            Location("test"),
            record_type,
            "refs",
        )
        self.assertEqual(
            token_pairs(lexer),
            [
                ("S_BRA", None),
                ("IDENTIFIER", "requ1"),
                ("AT", None),
                ("INTEGER", 26),
                ("COMMA", None),
                ("IDENTIFIER", "requ2"),
                ("AT", None),
                ("INTEGER", 27),
                ("COMMA", None),
                ("IDENTIFIER", "requ3"),
                ("AT", None),
                ("INTEGER", 28),
                ("COMMA", None),
                ("IDENTIFIER", "requ4"),
                ("AT", None),
                ("INTEGER", 29),
                ("COMMA", None),
                ("IDENTIFIER", "requ5"),
                ("COMMA", None),
                ("IDENTIFIER", "requ6"),
                ("COMMA", None),
                ("IDENTIFIER", "requ7"),
                ("S_KET", None),
            ],
        )

    def test_numeric_codebeamer_reference_array(self):
        stab = trlc_ast.Symbol_Table()
        package = trlc_ast.Package("DemoPkg", Location("test"), stab, False)
        record_type = trlc_ast.Record_Type(
            "Requirement", None, Location("test"), package, None, False
        )
        tuple_type = trlc_ast.Tuple_Type(
            "Codebeamer_Reference", None, Location("test"), package
        )
        for index, name in enumerate(("item_id", "version")):
            tuple_type.components.table[name] = trlc_ast.Composite_Component(
                name,
                None,
                Location("test"),
                tuple_type,
                trlc_ast.Builtin_Integer(),
                False,
            )
            if index == 0:
                tuple_type.add_separator(
                    trlc_ast.Separator(Token(Location("test"), "AT"))
                )
        array_type = trlc_ast.Array_Type(
            Location("test"),
            tuple_type,
            Location("test"),
            0,
            Location("test"),
            None,
        )
        record_type.components.table["references"] = trlc_ast.Composite_Component(
            "references",
            None,
            Location("test"),
            record_type,
            array_type,
            False,
        )

        lexer = MD_Lexer(self.mh, "test", "")
        lexer._emit_field_value(
            "[1234@25](codebeamer.md#1234),\n5678@26",
            Location("test"),
            record_type,
            "references",
        )

        self.assertEqual(
            token_pairs(lexer),
            [
                ("S_BRA", None),
                ("INTEGER", 1234),
                ("AT", None),
                ("INTEGER", 25),
                ("COMMA", None),
                ("INTEGER", 5678),
                ("AT", None),
                ("INTEGER", 26),
                ("S_KET", None),
            ],
        )

    def test_reference_link_destinations_with_parentheses(self):
        _stab, record_type = make_record_type()
        destinations = (
            "docs/req_(legacy).md",
            "docs/req_(legacy_(v2)).md",
            r"docs/req_\(legacy\).md",
            r"docs/req_legacy\).md",
            "docs/req_(legacy,archived).md",
        )
        for destination in destinations:
            for separator in (", ", "\n", "<br>"):
                with self.subTest(destination=destination, separator=separator):
                    lexer = MD_Lexer(self.mh, "test", "")
                    lexer._emit_field_value(
                        f"[requ1@26]({destination}){separator}[requ2](doc.md)",
                        Location("test"),
                        record_type,
                        "refs",
                    )
                    self.assertEqual(
                        token_pairs(lexer),
                        [
                            ("S_BRA", None),
                            ("IDENTIFIER", "requ1"),
                            ("AT", None),
                            ("INTEGER", 26),
                            ("COMMA", None),
                            ("IDENTIFIER", "requ2"),
                            ("S_KET", None),
                        ],
                    )

    def test_reference_link_targets_preserve_unclosed_destinations(self):
        for raw_value in (
            "[requ1@26](docs/req_(legacy).md",
            "[requ1@26](doc.md",
            "[requ1@26](doc.md\\",
        ):
            with self.subTest(raw_value=raw_value):
                self.assertEqual(
                    MD_Lexer._strip_array_link_targets(raw_value), raw_value
                )

    def test_string_field_preserves_link_destination_parentheses(self):
        _stab, record_type = make_record_type()
        raw_value = "[requ1@26](docs/req_(legacy).md)"
        lexer = MD_Lexer(self.mh, "test", "")
        lexer._emit_field_value(raw_value, Location("test"), record_type, "notes")
        self.assertEqual(token_pairs(lexer), [("STRING", raw_value)])

    def test_type_aware_field_emission(self):
        _stab, record_type = make_record_type()

        # String field: value stored as-is, no array heuristics applied
        # Tuple-array field: fully qualified references
        lexer = MD_Lexer(self.mh, "test", "")
        lexer._emit_field_value("Hello there", Location("test"), record_type, "notes")
        lexer._emit_field_value(
            "DemoPkg.item_a @ 1, DemoPkg.item_b @ 2",
            Location("test"),
            record_type,
            "refs",
        )
        self.assertEqual(
            token_pairs(lexer),
            [
                ("STRING", "Hello there"),
                ("S_BRA", None),
                ("IDENTIFIER", "DemoPkg"),
                ("DOT", None),
                ("IDENTIFIER", "item_a"),
                ("AT", None),
                ("INTEGER", 1),
                ("COMMA", None),
                ("IDENTIFIER", "DemoPkg"),
                ("DOT", None),
                ("IDENTIFIER", "item_b"),
                ("AT", None),
                ("INTEGER", 2),
                ("S_KET", None),
            ],
        )

        # Tuple-array field: unqualified (same-package) references
        lexer = MD_Lexer(self.mh, "test", "")
        lexer._emit_field_value(
            "item_a @ 1, item_b @ 2", Location("test"), record_type, "refs"
        )
        self.assertEqual(
            token_pairs(lexer),
            [
                ("S_BRA", None),
                ("IDENTIFIER", "item_a"),
                ("AT", None),
                ("INTEGER", 1),
                ("COMMA", None),
                ("IDENTIFIER", "item_b"),
                ("AT", None),
                ("INTEGER", 2),
                ("S_KET", None),
            ],
        )

        # Tuple-array field: mixed array (qualified + unqualified)
        lexer = MD_Lexer(self.mh, "test", "")
        lexer._emit_field_value(
            "item_a @ 1, OtherPkg.item_b @ 2", Location("test"), record_type, "refs"
        )
        self.assertEqual(
            token_pairs(lexer),
            [
                ("S_BRA", None),
                ("IDENTIFIER", "item_a"),
                ("AT", None),
                ("INTEGER", 1),
                ("COMMA", None),
                ("IDENTIFIER", "OtherPkg"),
                ("DOT", None),
                ("IDENTIFIER", "item_b"),
                ("AT", None),
                ("INTEGER", 2),
                ("S_KET", None),
            ],
        )

        # Heuristic fallback (_emit_value): unqualified must NOT be treated as array
        lexer = MD_Lexer(self.mh, "test", "")
        lexer._emit_value("item_a @ 1", Location("test"))
        self.assertEqual(token_pairs(lexer), [("STRING", "item_a @ 1")])

    def test_process_preamble_and_record(self):
        content = "\n".join(
            [
                "# DemoPkg",
                "import OtherPkg",
                "",
                "## Req_1",
                "| Property | Value |",
                "|----------|-------|",
                "| type | Requirement |",
                "| priority | 7 |",
                "",
                "### notes",
                "Hello, world!",
                "",
                "<hr>",
            ]
        )

        lexer = MD_Lexer(self.mh, "test.trlc.md", content)
        self.assertEqual(
            token_pairs(lexer),
            [
                ("KEYWORD", "#"),
                ("IDENTIFIER", "DemoPkg"),
                ("KEYWORD", "import"),
                ("IDENTIFIER", "OtherPkg"),
            ],
        )

        lexer.prepare_phase2(trlc_ast.Symbol_Table())

        self.assertEqual(
            token_pairs(lexer),
            [
                ("IDENTIFIER", "OtherPkg"),
                ("DOT", None),
                ("IDENTIFIER", "Requirement"),
                ("IDENTIFIER", "Req_1"),
                ("C_BRA", None),
                ("IDENTIFIER", "priority"),
                ("ASSIGN", None),
                ("INTEGER", 7),
                ("IDENTIFIER", "notes"),
                ("ASSIGN", None),
                ("STRING", "Hello, world!"),
                ("C_KET", None),
            ],
        )

    def test_markdown_recovery_skips_bad_record_and_keeps_valid_one(self):
        # lobster-trace: LRM.TRLC_Files
        # Recovery must skip a broken record and resume at the next valid record without
        # producing a second EOF/unexpected-brace error in the parser.
        stab = trlc_ast.Symbol_Table.create_global_table(self.mh)
        package = trlc_ast.Package("DemoPkg", Location("test"), stab, False)
        stab.table[trlc_ast.Symbol_Table.simplified_name(package.name)] = package

        record_type = trlc_ast.Record_Type(
            "Requirement",
            None,
            Location("test"),
            package,
            None,
            False,
        )
        package.symbols.table[trlc_ast.Symbol_Table.simplified_name("Requirement")] = (
            record_type
        )
        record_type.components.table["priority"] = trlc_ast.Composite_Component(
            "priority",
            None,
            Location("test"),
            record_type,
            trlc_ast.Builtin_Integer(),
            False,
        )
        record_type.components.table["notes"] = trlc_ast.Composite_Component(
            "notes",
            None,
            Location("test"),
            record_type,
            trlc_ast.Builtin_String(),
            False,
        )

        content = "\n".join(
            [
                "# DemoPkg",
                "",
                "## Bad_Req",
                "| Property | Value |",
                "|----------|-------|",
                "| priority | 7 |",
                "",
                "## Good_Req",
                "| Property | Value |",
                "|----------|-------|",
                "| type | Requirement |",
                "| priority | 7 |",
                "",
                "### notes",
                "ok",
                "",
                "<hr>",
            ]
        )

        lexer = MD_Lexer(self.mh, "test.trlc.md", content)
        parser = TrlcMarkdownParser(
            self.mh,
            stab,
            "test.trlc.md",
            lint_mode=True,
            error_recovery=True,
            primary_file=True,
            lexer=lexer,
        )
        parser.parse_preamble("trlc")
        lexer.prepare_phase2(stab)
        parser.ct = None
        parser.advance()

        self.assertTrue(parser.parse_trlc_file())
        self.assertEqual([obj.name for obj in parser.cu.items], ["Good_Req"])
        self.assertEqual(
            len(self.mh.messages),
            1,
        )
        self.assertEqual(
            self.mh.pop_message()[2],
            "record heading 'Bad_Req' has no 'type' property in its property table; record will be skipped",
        )

    def test_two_valid_records_are_separated_by_second_record_heading(self):
        stab = trlc_ast.Symbol_Table.create_global_table(self.mh)
        package = trlc_ast.Package("DemoPkg", Location("test"), stab, False)
        stab.table[trlc_ast.Symbol_Table.simplified_name(package.name)] = package

        for name in ("Requirement",):
            record_type = trlc_ast.Record_Type(
                name,
                None,
                Location("test"),
                package,
                None,
                False,
            )
            package.symbols.table[trlc_ast.Symbol_Table.simplified_name(name)] = (
                record_type
            )
            record_type.components.table["priority"] = trlc_ast.Composite_Component(
                "priority",
                None,
                Location("test"),
                record_type,
                trlc_ast.Builtin_Integer(),
                False,
            )
            record_type.components.table["notes"] = trlc_ast.Composite_Component(
                "notes",
                None,
                Location("test"),
                record_type,
                trlc_ast.Builtin_String(),
                False,
            )

        content = "\n".join(
            [
                "# DemoPkg",
                "",
                "## Req_1",
                "| Property | Value |",
                "|----------|-------|",
                "| type | Requirement |",
                "| priority | 7 |",
                "",
                "### notes",
                "first",
                "",
                "<hr>",
                "",
                "## Req_2",
                "| Property | Value |",
                "|----------|-------|",
                "| type | Requirement |",
                "| priority | 9 |",
                "",
                "### notes",
                "second",
                "",
                "<hr>",
            ]
        )

        lexer = MD_Lexer(self.mh, "test.trlc.md", content)
        parser = TrlcMarkdownParser(
            self.mh,
            stab,
            "test.trlc.md",
            lint_mode=True,
            error_recovery=True,
            primary_file=True,
            lexer=lexer,
        )
        parser.parse_preamble("trlc")
        lexer.prepare_phase2(stab)
        parser.ct = None
        parser.advance()

        self.assertTrue(parser.parse_trlc_file())
        self.assertEqual([obj.name for obj in parser.cu.items], ["Req_1", "Req_2"])

    def test_invalid_top_level_h4_heading_is_rejected(self):
        lexer = MD_Lexer(self.mh, "test.trlc.md", "# DemoPkg\n\n#### NotAllowed\n")

        with self.assertRaises(TRLC_Error) as exc:
            lexer.prepare_phase2(trlc_ast.Symbol_Table())

        self.assertEqual(
            self.mh.pop_message()[2],
            "heading level 4 and above is not valid in .trlc.md; use '##' for records and '###' for fields",
        )
        self.assertEqual(
            exc.exception.message,
            "heading level 4 and above is not valid in .trlc.md; use '##' for records and '###' for fields",
        )

    def test_invalid_h4_heading_outside_field_is_rejected(self):
        lexer = MD_Lexer(self.mh, "test.trlc.md", "# DemoPkg\n\n#### NotAllowed\n")

        with self.assertRaises(TRLC_Error):
            lexer.prepare_phase2(trlc_ast.Symbol_Table())

        self.assertEqual(
            self.mh.pop_message()[2],
            "heading level 4 and above is not valid in .trlc.md; use '##' for records and '###' for fields",
        )

    def test_process_heading_based_tuple_array_fields(self):
        content = "\n".join(
            [
                "# DemoPkg",
                "",
                "## req_parent",
                "| Property | Value |",
                "|----------|-------|",
                "| type | Requirement |",
                "| description | parent requirement |",
                "",
                "### derived_from",
                "[requ1@26](document.md#requ1)",
                "requ2@27",
                "requ3@28",
                "[requ4@29](to-be-ignored.md#whatever)",
                "requ5",
                "[requ6](also-to-be-ignored.md#whatever)",
                "[requ7](some totally unrelated string shall also be ignored in this first MVP)",
                "",
                "### some_other_array_field",
                "requ1, requ2, requ3, [requ4@29](to-be-ignored.md#whatever), requ5, [requ6](also-to-be-ignored.md#whatever), [requ7](abcdef)",
            ]
        )

        lexer = MD_Lexer(self.mh, "test.trlc.md", content)

        stab = trlc_ast.Symbol_Table()
        package = trlc_ast.Package("DemoPkg", Location("test"), stab, False)
        record_type = trlc_ast.Record_Type(
            "Requirement", None, Location("test"), package, None, False
        )

        for name in ("derived_from", "some_other_array_field"):
            tuple_type = trlc_ast.Tuple_Type(
                "TupleType", None, Location("test"), package
            )
            array_type = trlc_ast.Array_Type(
                Location("test"),
                tuple_type,
                Location("test"),
                0,
                Location("test"),
                None,
            )
            record_type.components.table[
                trlc_ast.Symbol_Table.simplified_name(name)
            ] = trlc_ast.Composite_Component(
                name,
                None,
                Location("test"),
                record_type,
                array_type,
                False,
            )

        package.symbols.table[trlc_ast.Symbol_Table.simplified_name("Requirement")] = (
            record_type
        )
        stab.table[trlc_ast.Symbol_Table.simplified_name(package.name)] = package

        lexer.prepare_phase2(stab)

        def ref(name, version=None):
            if version is None:
                return [("IDENTIFIER", name)]
            return [("IDENTIFIER", name), ("AT", None), ("INTEGER", version)]

        def array(*entries):
            result = [("S_BRA", None)]
            for idx, entry in enumerate(entries):
                if idx:
                    result.append(("COMMA", None))
                result.extend(entry)
            result.append(("S_KET", None))
            return result

        self.assertEqual(
            token_pairs(lexer),
            [
                ("IDENTIFIER", "Requirement"),
                ("IDENTIFIER", "req_parent"),
                ("C_BRA", None),
                ("IDENTIFIER", "description"),
                ("ASSIGN", None),
                ("STRING", "parent requirement"),
                ("IDENTIFIER", "derived_from"),
                ("ASSIGN", None),
            ]
            + array(
                ref("requ1", 26),
                ref("requ2", 27),
                ref("requ3", 28),
                ref("requ4", 29),
                ref("requ5"),
                ref("requ6"),
                ref("requ7"),
            )
            + [("IDENTIFIER", "some_other_array_field"), ("ASSIGN", None)]
            + array(
                ref("requ1"),
                ref("requ2"),
                ref("requ3"),
                ref("requ4", 29),
                ref("requ5"),
                ref("requ6"),
                ref("requ7"),
            )
            + [("C_KET", None)],
        )

    def test_untyped_heuristics_do_not_treat_bare_references_as_array(self):
        lexer = MD_Lexer(self.mh, "test", "")
        lexer._emit_value("item", Location("test"))
        lexer._emit_value("Pkg.item", Location("test"))
        lexer._emit_value("Revision : 12", Location("test"))
        self.assertEqual(
            token_pairs(lexer),
            [
                ("IDENTIFIER", "item"),
                ("IDENTIFIER", "Pkg"),
                ("DOT", None),
                ("IDENTIFIER", "item"),
                ("STRING", "Revision : 12"),
            ],
        )

    def test_markdown_link_emission_depends_on_field_type(self):
        _stab, record_type = make_record_type()
        raw_value = "[Pkg.item @ 1](doc.md)"
        lexer = MD_Lexer(self.mh, "test", "")
        lexer._emit_field_value(raw_value, Location("test"), record_type, "refs")
        lexer._emit_field_value(raw_value, Location("test"), record_type, "notes")
        self.assertEqual(
            token_pairs(lexer),
            [
                ("S_BRA", None),
                ("IDENTIFIER", "Pkg"),
                ("DOT", None),
                ("IDENTIFIER", "item"),
                ("AT", None),
                ("INTEGER", 1),
                ("S_KET", None),
                ("STRING", raw_value),
            ],
        )

    def test_invalid_entry_in_tuple_array_field_is_reported(self):
        _stab, record_type = make_record_type()

        lexer = MD_Lexer(self.mh, "test", "")
        lexer._emit_field_value(
            "[req 1](doc.md), requ2 @ 3",
            Location("test"),
            record_type,
            "refs",
        )
        self.assertEqual(token_pairs(lexer), [("S_BRA", None), ("S_KET", None)])
        self.assertEqual(len(self.mh.messages), 1)
        self.assertEqual(
            self.mh.pop_message()[2],
            "invalid entry 'req 1' in tuple-reference array field 'refs'",
        )

    def test_preamble_nested_package_and_wildcard_import(self):
        # lobster-trace: LRM.Nested_Package_Names
        # lobster-trace: LRM.Wildcard_Import
        content = "\n".join(
            [
                "# ns.app",
                "import ns.base",
                "import ns.*",
                "",
                "<hr>",
            ]
        )

        lexer = MD_Lexer(self.mh, "test.trlc.md", content)
        self.assertEqual(
            token_pairs(lexer),
            [
                ("KEYWORD", "#"),
                ("IDENTIFIER", "ns"),
                ("DOT", None),
                ("IDENTIFIER", "app"),
                ("KEYWORD", "import"),
                ("IDENTIFIER", "ns"),
                ("DOT", None),
                ("IDENTIFIER", "base"),
                ("KEYWORD", "import"),
                ("IDENTIFIER", "ns"),
                ("DOT", None),
                ("OPERATOR", "*"),
            ],
        )

    def test_preamble_package_name_tokens_have_per_segment_locations(self):
        # lobster-trace: LRM.Nested_Package_Names
        # Each segment/dot of a nested package name must carry its own
        # location, so diagnostics later on (e.g. an unknown symbol in
        # "ns.app") point a caret at the offending segment instead of a
        # single location shared by the whole name.
        lexer = MD_Lexer(self.mh, "test.trlc.md", "# ns.app\n")
        cols = [
            (token.kind, token.value, token.location.line_no, token.location.col_no)
            for token in all_tokens(lexer)
        ]
        self.assertEqual(
            cols,
            [
                ("KEYWORD", "#", 1, 1),
                ("IDENTIFIER", "ns", 1, 3),
                ("DOT", None, 1, 5),
                ("IDENTIFIER", "app", 1, 6),
            ],
        )

    def test_preamble_import_name_offset_not_confused_by_keyword_substring(self):
        # lobster-trace: LRM.Nested_Package_Names
        # The package name "rt" also occurs as a substring inside the
        # "import" keyword itself (at index 4). The offset of the
        # imported name must be computed positionally, not via a
        # substring search that could match that unrelated occurrence.
        lexer = MD_Lexer(self.mh, "test.trlc.md", "# app\n\nimport rt\n")
        tokens = all_tokens(lexer)
        import_ident = tokens[-1]
        self.assertEqual((import_ident.kind, import_ident.value), ("IDENTIFIER", "rt"))
        self.assertEqual(import_ident.location.line_no, 3)
        self.assertEqual(import_ident.location.col_no, 8)

    def test_preamble_import_break_tags_are_treated_as_newlines(self):
        lexer = MD_Lexer(
            self.mh, "test.trlc.md", "# app\nimport first<br>import second\n"
        )
        self.assertEqual(
            token_pairs(lexer),
            [
                ("KEYWORD", "#"),
                ("IDENTIFIER", "app"),
                ("KEYWORD", "import"),
                ("IDENTIFIER", "first"),
                ("KEYWORD", "import"),
                ("IDENTIFIER", "second"),
            ],
        )

    def test_preamble_import_break_tags_keep_per_import_locations(self):
        lexer = MD_Lexer(
            self.mh, "test.trlc.md", "# app\nimport first<br>import second\n"
        )
        cols = [
            (token.kind, token.value, token.location.line_no, token.location.col_no)
            for token in all_tokens(lexer)
        ]
        self.assertEqual(
            cols,
            [
                ("KEYWORD", "#", 1, 1),
                ("IDENTIFIER", "app", 1, 3),
                ("KEYWORD", "import", 2, 1),
                ("IDENTIFIER", "first", 2, 8),
                ("KEYWORD", "import", 2, 17),
                ("IDENTIFIER", "second", 2, 24),
            ],
        )

    def test_preamble_import_extra_spaces_do_not_shift_name_location(self):
        # Measure the offset from the real whitespace, not a fixed space count;
        # otherwise the diagnostic points at the whitespace instead of the name.
        lexer = MD_Lexer(self.mh, "test.trlc.md", "# app\nimport    base\n")
        tokens = all_tokens(lexer)
        import_ident = tokens[-1]
        self.assertEqual(
            (import_ident.kind, import_ident.value), ("IDENTIFIER", "base")
        )
        self.assertEqual(import_ident.location.line_no, 2)
        self.assertEqual(import_ident.location.col_no, 11)

    def test_preamble_import_break_tags_with_extra_spaces_keep_locations(self):
        # Same regression as above, but for a later clause on a line that
        # also uses a break tag, to make sure the per-clause offset isn't
        # reused from the first clause's position either.
        lexer = MD_Lexer(
            self.mh, "test.trlc.md", "# app\nimport first<br>import    second\n"
        )
        cols = [
            (token.kind, token.value, token.location.line_no, token.location.col_no)
            for token in all_tokens(lexer)
        ]
        self.assertEqual(
            cols,
            [
                ("KEYWORD", "#", 1, 1),
                ("IDENTIFIER", "app", 1, 3),
                ("KEYWORD", "import", 2, 1),
                ("IDENTIFIER", "first", 2, 8),
                ("KEYWORD", "import", 2, 17),
                ("IDENTIFIER", "second", 2, 27),
            ],
        )

    def test_preamble_import_only_genuine_break_tags_act_as_separators(self):
        # Only real <br> tags may split import clauses; fake HTML-like tags
        # should raise an error instead of being silently accepted.
        with self.assertRaises(TRLC_Error):
            MD_Lexer(self.mh, "test.trlc.md", "# app\nimport base<xyz>import support\n")

        self.assertEqual(self.mh.pop_message()[2], "unexpected character '<'")

    def test_preamble_import_break_tag_between_keyword_and_name_is_rejected(self):
        # <br> is only a valid separator between/after complete "import
        # <name>" clauses; it must not be silently accepted between the
        # "import" keyword and the package name.
        with self.assertRaises(TRLC_Error):
            MD_Lexer(self.mh, "test.trlc.md", "# app\nimport <br> base\n")
        location, kind, message = self.mh.pop_message()
        self.assertEqual(kind, Kind.SYS_ERROR)
        self.assertEqual(
            message, "a <br> tag is not allowed between 'import' and the package name"
        )
        self.assertEqual(location.line_no, 2)
        self.assertEqual(location.col_no, 8)

    def test_preamble_import_break_tags_keyword_is_case_sensitive(self):
        # Only a literal lowercase "import" may start a later clause; a
        # case-insensitive match would wrongly accept "IMPORT".
        lexer = MD_Lexer(
            self.mh, "test.trlc.md", "# app\nimport first<br>IMPORT second\n"
        )
        self.assertEqual(
            token_pairs(lexer),
            [
                ("KEYWORD", "#"),
                ("IDENTIFIER", "app"),
                ("KEYWORD", "import"),
                ("IDENTIFIER", "first"),
            ],
        )

    def test_preamble_invalid_segment_in_nested_name_points_at_offending_char(self):
        # lobster-trace: LRM.Nested_Package_Names
        # Regression test for the caret fix: the error must point at the
        # invalid character within the second segment, not at the start
        # of the whole package name.
        with self.assertRaises(TRLC_Error):
            MD_Lexer(self.mh, "test.trlc.md", "# ns.1bad\n")
        location, kind, message = self.mh.pop_message()
        self.assertEqual(kind, Kind.SYS_ERROR)
        self.assertEqual(message, "unexpected character '1'")
        self.assertEqual(location.line_no, 1)
        self.assertEqual(location.col_no, 6)

    def test_preamble_invalid_package_name(self):
        # lobster-trace: LRM.Nested_Package_Names
        with self.assertRaises(TRLC_Error):
            MD_Lexer(self.mh, "test.trlc.md", "# ns..app\n")
        location, kind, message = self.mh.pop_message()
        self.assertEqual(kind, Kind.SYS_ERROR)
        self.assertEqual(message, "expected identifier")
        self.assertEqual(location.line_no, 1)

    def test_preamble_package_heading_must_be_single_word(self):
        # lobster-trace: LRM.Nested_Package_Names
        with self.assertRaises(TRLC_Error):
            MD_Lexer(self.mh, "test.trlc.md", "# ns app\n")
        _, kind, message = self.mh.pop_message()
        self.assertEqual(kind, Kind.SYS_ERROR)
        self.assertEqual(message, "package heading must be '# <PackageName>'")

    def test_type_row_tokens_use_type_row_location(self):
        content = "\n".join(
            [
                "# DemoPkg",
                "",
                "## Req_1",
                "",
                "| Property | Value |",
                "|----------|-------|",
                "| type | Requirement |",
                "| priority | 7 |",
            ]
        )

        lexer = MD_Lexer(self.mh, "test.trlc.md", content)
        lexer.prepare_phase2(trlc_ast.Symbol_Table())

        tokens = []
        while True:
            token = lexer.token()
            if token is None:
                break
            tokens.append(token)

        type_row_tokens = [token for token in tokens if token.location.line_no == 7]
        heading_tokens = [token for token in tokens if token.location.line_no == 3]

        self.assertEqual(
            [(token.kind, token.value) for token in type_row_tokens],
            [("IDENTIFIER", "Requirement")],
        )

        self.assertEqual(
            [(token.kind, token.value) for token in heading_tokens[-2:]],
            [
                ("IDENTIFIER", "Req_1"),
                ("C_BRA", None),
            ],
        )


if __name__ == "__main__":
    unittest.main()
