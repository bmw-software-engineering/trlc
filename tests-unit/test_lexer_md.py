import unittest
from fractions import Fraction

from trlc import ast as trlc_ast
from trlc.errors import Location, Message_Handler, TRLC_Error, Kind
from trlc.lexer_md import MD_Lexer


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
        self.assertEqual(MD_Lexer._parse_heading("### Record Name"), (3, "Record Name"))
        self.assertEqual(MD_Lexer._parse_heading("## Section"), (2, "Section"))
        self.assertEqual(MD_Lexer._parse_heading("###"), (0, None))
        self.assertEqual(MD_Lexer._parse_heading("#NotAHeading"), (0, None))

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

    def test_process_preamble_section_and_record(self):
        content = "\n".join(
            [
                "# DemoPkg",
                "import OtherPkg",
                "",
                "## Overview",
                "",
                "### Req_1",
                "| Property | Value |",
                "|----------|-------|",
                "| type | Requirement |",
                "| priority | 7 |",
                "",
                "#### notes",
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
                ("KEYWORD", "##"),
                ("STRING", "Overview"),
                ("C_BRA", None),
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
                ("C_KET", None),
            ],
        )

    def test_type_row_tokens_use_type_row_location(self):
        content = "\n".join(
            [
                "# DemoPkg",
                "",
                "## Overview",
                "",
                "### Req_1",
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

        type_row_tokens = [token for token in tokens if token.location.line_no == 9]
        heading_tokens = [token for token in tokens if token.location.line_no == 5]

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
