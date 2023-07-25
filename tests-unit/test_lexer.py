import unittest

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

    def match(self, kind, value):
        self.assertGreater(len(self.tokens), 0)
        token, self.tokens = self.tokens[0], self.tokens[1:]
        self.assertEqual(token.kind, kind,
                         "%s does not have the right kind" % str(token))
        if value is not None:
            self.assertEqual(token.value, value)

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
