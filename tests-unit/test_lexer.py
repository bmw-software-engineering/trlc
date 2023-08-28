import unittest
import re
from fractions import Fraction

from trlc.errors import Location, Message_Handler, TRLC_Error
from trlc.lexer import TRLC_Lexer


class List_Handler(Message_Handler):
    def __init__(self):
        super().__init__()
        self.messages = []

    def emit(self, location, kind, message, fatal=True, extrainfo=None):
        assert isinstance(location, Location)
        assert isinstance(kind, str)
        assert isinstance(message, str)
        assert isinstance(fatal, bool)
        assert isinstance(extrainfo, str) or extrainfo is None

        self.messages.append((location, kind, message))

        if fatal:
            raise TRLC_Error(location, kind, message)

    def pop_message(self):
        assert self.messages
        message, self.messages = self.messages[0], self.messages[1:]
        return message


class Test_Lexer(unittest.TestCase):
    def setUp(self):
        self.mh    = List_Handler()
        self.lexer = None

    def tearDown(self):
        self.assertEqual(len(self.mh.messages),
                         0,
                         "unexpected messages: %s" %
                         (", ".join(msg[2]
                                    for msg in self.mh.messages)))
        self.assertEqual(len(self.tokens),
                         0,
                         "unexpected tokens: %s" %
                         (", ".join(map(str, self.tokens))))

    def input(self, content):
        assert isinstance(content, str)
        self.lexer = TRLC_Lexer(self.mh, "test", content)
        self.tokens = []
        while True:
            token = self.lexer.token()
            if token:
                self.tokens.append(token)
            else:
                break

    def matchError(self, expected_message):
        self.assertGreater(len(self.mh.messages), 0)
        loc, kind, message = self.mh.pop_message()
        self.assertEqual(message, expected_message)

    def match(self, kind, value=None):
        self.assertGreater(len(self.tokens), 0)
        token, self.tokens = self.tokens[0], self.tokens[1:]
        self.assertEqual(token.kind, kind,
                         "%s does not have the right kind" % str(token))
        if value is not None:
            self.assertEqual(token.value, value)
        return token

    def testIdentifiers1(self):
        # lobster-trace: LRM.Identifier
        # lobster-trace: LRM.Integers
        with self.assertRaises(TRLC_Error):
            self.input("7_b")
        self.matchError("b is not a valid base 10 digit")

    def testIdentifiers2(self):
        # lobster-trace: LRM.Identifier
        self.input("fo_ b4r")
        self.match("IDENTIFIER", "fo_")
        self.match("IDENTIFIER", "b4r")

    def testIdentifiers3(self):
        # lobster-trace: LRM.Builtin_Identifier
        with self.assertRaises(TRLC_Error):
            self.input("foo:bar")
        self.matchError("builtin function name must start with trlc:")

    def testIdentifiers4(self):
        # lobster-trace: LRM.Identifier
        with self.assertRaises(TRLC_Error):
            self.input("_foo_")
        self.matchError("unexpected character '_'")

    def testKeywords(self):
        # lobster-trace: LRM.TRLC_Keywords
        bullets = [
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
        ]
        self.input(" ".join(bullets))
        for kw in bullets:
            self.match("KEYWORD", kw)

    def testPunctuationSingle(self):
        # lobster-trace: LRM.Single_Delimiters
        bullets = [
            "Brackets: `(` `)` `[` `]` `{` `}`",
            "Punctuation: `,` `.` `=`",
            "Operators: `*` `/` `%` `+` `-`",
            "Boolean operators: `<` `>`",
            "Symbols: `@` `:` `;`",
        ]
        self.input(" ".join(" ".join(re.findall(r"`(.*?)`", item))
                            for item in bullets))
        self.match("BRA")
        self.match("KET")
        self.match("S_BRA")
        self.match("S_KET")
        self.match("C_BRA")
        self.match("C_KET")
        self.match("COMMA")
        self.match("DOT")
        self.match("ASSIGN")
        self.match("OPERATOR")
        self.match("OPERATOR")
        self.match("OPERATOR")
        self.match("OPERATOR")
        self.match("OPERATOR")
        self.match("OPERATOR")
        self.match("OPERATOR")
        self.match("AT")
        self.match("COLON")
        self.match("SEMICOLON")

    def testPunctuationDouble(self):
        # lobster-trace: LRM.Double_Delimiters
        # lobster-trace: LRM.Lexing_Disambiguation
        bullets = [
            "Operators: `**`",
            "Boolean operators: `==` `<=` `>=` `!=`",
            "Punctuation: `=>` `..`"
        ]
        self.input(" ".join(" ".join(re.findall(r"`(.*?)`", item))
                            for item in bullets))
        self.match("OPERATOR")
        self.match("OPERATOR")
        self.match("OPERATOR")
        self.match("OPERATOR")
        self.match("OPERATOR")
        self.match("ARROW")
        self.match("RANGE")

    def testIncompleteNEQ(self):
        # lobster-trace: LRM.Double_Delimiters
        with self.assertRaises(TRLC_Error):
            self.input("foo ! bar")
        self.matchError("malformed != operator")
        self.match("IDENTIFIER")

    def testIntegers1(self):
        # lobster-trace: LRM.Integers
        self.input("0 0b0100 10_000 0xdeadbeef")
        self.match("INTEGER", 0)
        self.match("INTEGER", 4)
        self.match("INTEGER", 10000)
        self.match("INTEGER", 0xdeadbeef)

    def testIntegers2(self):
        # lobster-trace: LRM.Integers
        with self.assertRaises(TRLC_Error):
            self.input("0b_")
        self.matchError("base 2 digit is required here")

    def testIntegers3(self):
        # lobster-trace: LRM.Integers
        self.input("0..1")
        self.match("INTEGER")
        self.match("RANGE")
        self.match("INTEGER")

    def testIntegers4(self):
        # lobster-trace: LRM.Integers
        with self.assertRaises(TRLC_Error):
            self.input("0b")
        self.matchError("unfinished base 2 integer")

    def testDecimals1(self):
        # lobster-trace: LRM.Decimals
        self.input("0.0 010.010 10_000.000_1")
        self.match("DECIMAL", Fraction(0))
        self.match("DECIMAL", Fraction("10.01"))
        self.match("DECIMAL", Fraction("10000.0001"))

    def testDecimals2(self):
        # lobster-trace: LRM.Decimals
        with self.assertRaises(TRLC_Error):
            self.input("0x0.3")
        self.matchError("base 16 integer may not contain a decimal point")

    def testDecimals3(self):
        # lobster-trace: LRM.Decimals
        with self.assertRaises(TRLC_Error):
            self.input("0.1.2")
        self.matchError("decimal point is not allowed here")

    def testStrings1(self):
        # lobster-trace: LRM.Strings
        # lobster-trace: LRM.Simple_String_Value
        with self.assertRaises(TRLC_Error):
            self.input('''
               "potato" "pot\\"ato" "no\\nescape"
               "foo\nbar"
            ''')
        self.matchError("double quoted strings cannot include newlines")
        self.match("STRING", r'potato')
        self.match("STRING", r'pot"ato')
        self.match("STRING", r'no\nescape')

    def testStrings2(self):
        # lobster-trace: LRM.Strings
        # lobster-trace: LRM.Complex_String_Value
        self.input("""
          '''This is a
               * complex
               * string
             Potato.
          '''
        """)
        self.match("STRING",
                   "This is a\n  * complex\n  * string\nPotato.")

    def testStrings3(self):
        # lobster-trace: LRM.Strings
        with self.assertRaises(TRLC_Error):
            self.input('"foo')
        self.matchError("unterminated string")

    def testStrings4(self):
        # lobster-trace: LRM.Strings
        with self.assertRaises(TRLC_Error):
            self.input("'''foo")
        self.matchError("unterminated triple-quoted string")

    def testStrings5(self):
        # lobster-trace: LRM.Strings
        with self.assertRaises(TRLC_Error):
            self.input("'potato'")
        self.matchError("malformed triple-quoted string")

    def testStrings6(self):
        # lobster-trace: LRM.Strings
        # lobster-trace: LRM.Complex_String_Value
        self.input("""
          '''

          '''
        """)
        self.match("STRING", "")

    def testComment(self):
        # lobster-trace: LRM.Comments
        self.input("""foo /* bar""")
        self.match("IDENTIFIER")
        self.match("COMMENT")

    def testLocation1(self):
        self.input("""foo '''bar\nbaz''' bork""")
        t = self.match("IDENTIFIER")
        self.assertEqual(t.location.line_no, 1)
        self.assertEqual(t.location.col_no, 1)
        end = t.location.get_end_location()
        self.assertEqual(end.line_no, 1)
        self.assertEqual(end.col_no, 3)

        t = self.match("STRING")
        self.assertEqual(t.location.line_no, 1)
        self.assertEqual(t.location.col_no, 5)
        end = t.location.get_end_location()
        self.assertEqual(end.line_no, 2)
        self.assertEqual(end.col_no, 6)

        t = self.match("IDENTIFIER")
        self.assertEqual(t.location.line_no, 2)
        self.assertEqual(t.location.col_no, 8)
        end = t.location.get_end_location()
        self.assertEqual(end.line_no, 2)
        self.assertEqual(end.col_no, 11)
