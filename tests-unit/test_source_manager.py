import os
import tempfile
import unittest

from trlc.errors import Message_Handler
from trlc.trlc import Source_Manager


class Test_Register_Include_Files(unittest.TestCase):
    def setUp(self):
        self.mh = Message_Handler()
        self.sm = Source_Manager(self.mh)

    def testNotAListRaisesTypeError(self):
        with self.assertRaises(TypeError) as ctx:
            self.sm.register_include_files("not_a_list.rsl")
        self.assertIn("list", str(ctx.exception))

    def testItemNotStringRaisesTypeError(self):
        with self.assertRaises(TypeError) as ctx:
            self.sm.register_include_files([42])
        self.assertIn("string", str(ctx.exception))

    def testMissingFileRaisesFileNotFound(self):
        with self.assertRaises(FileNotFoundError) as ctx:
            self.sm.register_include_files(["/does/not/exist.rsl"])
        self.assertIn("does not exist", str(ctx.exception).lower())

    def testNonRslTrlcFileIsIgnored(self):
        with tempfile.NamedTemporaryFile(suffix=".txt", delete=False) as f:
            txt_path = f.name
        try:
            self.sm.register_include_files([txt_path])
            self.assertNotIn(os.path.abspath(txt_path), self.sm.includes)
        finally:
            os.unlink(txt_path)

    def testRslFileIsRegistered(self):
        with tempfile.NamedTemporaryFile(suffix=".rsl", delete=False) as f:
            rsl_path = f.name
        try:
            self.sm.register_include_files([rsl_path])
            self.assertIn(os.path.abspath(rsl_path), self.sm.includes)
        finally:
            os.unlink(rsl_path)

    def testTrlcFileIsRegistered(self):
        with tempfile.NamedTemporaryFile(suffix=".trlc", delete=False) as f:
            trlc_path = f.name
        try:
            self.sm.register_include_files([trlc_path])
            self.assertIn(os.path.abspath(trlc_path), self.sm.includes)
        finally:
            os.unlink(trlc_path)

    def testEmptyListIsValid(self):
        self.sm.register_include_files([])
        self.assertEqual(self.sm.includes, {})

    def testMultipleFilesAllRegistered(self):
        paths = []
        try:
            for suffix in (".rsl", ".trlc"):
                f = tempfile.NamedTemporaryFile(suffix=suffix, delete=False)
                f.close()
                paths.append(f.name)
            self.sm.register_include_files(paths)
            for p in paths:
                self.assertIn(os.path.abspath(p), self.sm.includes)
        finally:
            for p in paths:
                os.unlink(p)

    def testStopsAtFirstMissingFile(self):
        with tempfile.NamedTemporaryFile(suffix=".rsl", delete=False) as f:
            rsl_path = f.name
        try:
            with self.assertRaises(FileNotFoundError):
                self.sm.register_include_files([rsl_path, "/no/such/file.rsl"])
            self.assertIn(os.path.abspath(rsl_path), self.sm.includes)
        finally:
            os.unlink(rsl_path)
