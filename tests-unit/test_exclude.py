import os
import shutil
import tempfile
import unittest

from trlc.errors import Kind, Message_Handler, TRLC_Error
from trlc.trlc import Source_Manager


class List_Handler(Message_Handler):
    def __init__(self):
        super().__init__()
        self.messages = []

    def emit(self, location, kind, message, fatal=True, extrainfo=None, category=None):
        self.messages.append((kind, message))
        if fatal:
            raise TRLC_Error(location, kind, message)

    def has_error(self):
        return any(k in (Kind.SYS_ERROR, Kind.USER_ERROR) for k, _ in self.messages)

    def error_messages(self):
        return [m for k, m in self.messages if k in (Kind.SYS_ERROR, Kind.USER_ERROR)]


def make_source_manager(lint_mode=True):
    mh = List_Handler()
    return Source_Manager(mh=mh, lint_mode=lint_mode, error_recovery=False), mh


class Test_Exclude(unittest.TestCase):
    """Tests for excluding files and directories from processing."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp()

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def write(self, name, content):
        path = os.path.join(self.tmp, name)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
        return path

    def test_is_path_excluded_unknown_path(self):
        sm, _ = make_source_manager()
        self.assertFalse(sm.is_path_excluded(self.tmp))

    def test_exclude_path_requires_string(self):
        sm, _ = make_source_manager()
        with self.assertRaisesRegex(TypeError, "path_name must be a string"):
            sm.exclude_path(None)

    def test_is_path_excluded_requires_string(self):
        sm, _ = make_source_manager()
        with self.assertRaisesRegex(TypeError, "path_name must be a string"):
            sm.is_path_excluded(None)

    def test_exclude_file_directly(self):
        sm, _ = make_source_manager()
        file_name = self.write("foo.rsl", "package Foo\n")
        sm.exclude_path(file_name)
        self.assertTrue(sm.is_path_excluded(file_name))

    def test_exclude_directory_covers_contents(self):
        sm, _ = make_source_manager()
        nested_dir = os.path.join(self.tmp, "nested")
        nested_file = self.write("nested/foo.rsl", "package Foo\n")
        sm.exclude_path(nested_dir)
        self.assertTrue(sm.is_path_excluded(nested_dir))
        self.assertTrue(sm.is_path_excluded(nested_file))

    def test_exclude_does_not_affect_siblings(self):
        sm, _ = make_source_manager()
        excluded_dir = os.path.join(self.tmp, "excluded")
        sibling_file = self.write("kept/foo.rsl", "package Foo\n")
        sm.exclude_path(excluded_dir)
        self.assertFalse(sm.is_path_excluded(sibling_file))

    def test_register_directory_skips_excluded_subdirectory(self):
        sm, mh = make_source_manager()
        self.write("foo.rsl", "package Foo\n")
        self.write("excluded/bar.rsl", "package Bar\n")
        sm.exclude_path(os.path.join(self.tmp, "excluded"))

        ok = sm.register_directory(self.tmp)
        self.assertTrue(ok, mh.error_messages())
        self.assertEqual(len(sm.rsl_files), 1)
        self.assertIn(
            os.path.abspath(os.path.join(self.tmp, "foo.rsl")),
            sm.rsl_files,
        )

    def test_register_directory_skips_excluded_file(self):
        sm, mh = make_source_manager()
        self.write("foo.rsl", "package Foo\n")
        bar_file = self.write("bar.rsl", "package Bar\n")
        sm.exclude_path(bar_file)

        ok = sm.register_directory(self.tmp)
        self.assertTrue(ok, mh.error_messages())
        self.assertEqual(len(sm.rsl_files), 1)
        self.assertNotIn(os.path.abspath(bar_file), sm.rsl_files)

    def test_register_include_skips_excluded_subdirectory(self):
        sm, _ = make_source_manager()
        self.write("foo.rsl", "package Foo\n")
        self.write("excluded/bar.rsl", "package Bar\n")
        sm.exclude_path(os.path.join(self.tmp, "excluded"))

        sm.register_include(self.tmp)
        self.assertEqual(len(sm.includes), 1)
        self.assertIn(
            os.path.abspath(os.path.join(self.tmp, "foo.rsl")),
            sm.includes,
        )

    def test_register_include_skips_excluded_file(self):
        sm, _ = make_source_manager()
        self.write("foo.rsl", "package Foo\n")
        bar_file = self.write("bar.rsl", "package Bar\n")
        sm.exclude_path(bar_file)

        sm.register_include(self.tmp)
        self.assertEqual(len(sm.includes), 1)
        self.assertNotIn(os.path.abspath(bar_file), sm.includes)


if __name__ == "__main__":
    unittest.main()
