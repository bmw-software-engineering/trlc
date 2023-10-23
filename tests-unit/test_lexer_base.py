import unittest
import re

from trlc.errors import Message_Handler
from trlc.lexer import Lexer_Base


class Potato(Lexer_Base):
    def file_location(self):
        pass

    def token(self):
        pass


class Test_Lexer_Base(unittest.TestCase):
    def setUp(self):
        self.lexer = Potato(mh      = Message_Handler(),
                            content = "")
        self.test_range = 0xffff

    def tearDown(self):
        pass

    @staticmethod
    def reference_is_alpha(char):
        assert isinstance(char, str) and len(char) == 1
        return ord('a') <= ord(char) <= ord('z') or \
            ord('A') <= ord(char) <= ord('Z')

    @staticmethod
    def reference_is_numeric(char):
        assert isinstance(char, str) and len(char) == 1
        return ord('0') <= ord(char) <= ord('9')

    @staticmethod
    def reference_is_alnum(char):
        assert isinstance(char, str) and len(char) == 1
        return ord('a') <= ord(char) <= ord('z') or \
            ord('A') <= ord(char) <= ord('Z') or \
            ord('0') <= ord(char) <= ord('9')

    def testIsAlpha(self):
        for i in range(self.test_range):
            c = chr(i)
            self.assertEqual(self.reference_is_alpha(c),
                             self.lexer.is_alpha(c),
                             "mismatch for codepoint %u (%s)" % (i, repr(c)))

    def testIsDigit(self):
        for i in range(self.test_range):
            c = chr(i)
            self.assertEqual(self.reference_is_numeric(c),
                             self.lexer.is_numeric(c),
                             "mismatch for codepoint %u (%s)" % (i, repr(c)))

    def testIsAlnum(self):
        for i in range(self.test_range):
            c = chr(i)
            self.assertEqual(self.reference_is_alnum(c),
                             self.lexer.is_alnum(c),
                             "mismatch for codepoint %u (%s)" % (i, repr(c)))
