import contextlib
import io
import os
import shutil
import sys
import tempfile
import unittest

from trlc.errors import Kind, Message_Handler, TRLC_Error
from trlc.trlc import Source_Manager, trlc as trlc_main


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
        sm, mh = make_source_manager()
        self.write("foo.rsl", "package Foo\n")
        self.write("excluded/bar.rsl", "package Bar\n")
        sm.exclude_path(os.path.join(self.tmp, "excluded"))

        self.assertFalse(sm.register_include(self.tmp))
        self.assertTrue(mh.has_error())
        self.assertEqual(len(sm.includes), 0)

    def test_register_include_fails_on_excluded_file(self):
        sm, mh = make_source_manager()
        self.write("foo.rsl", "package Foo\n")
        bar_file = self.write("bar.rsl", "package Bar\n")
        sm.exclude_path(bar_file)

        self.assertFalse(sm.register_include(self.tmp))
        self.assertTrue(mh.has_error())
        self.assertNotIn(os.path.abspath(bar_file), sm.includes)


class Test_Exclude_From_File(unittest.TestCase):
    """Tests for the --exclude-from-file command line option."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.write("foo.rsl", "package Foo\n")
        self.write("skip/bar.rsl", "not valid trlc\n")
        self.write("baz.rsl", "not valid trlc either\n")

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def write(self, name, content):
        path = os.path.join(self.tmp, name)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
        return path

    def run_cli(self, *args):
        out = io.StringIO()
        err = io.StringIO()
        old_argv = sys.argv
        sys.argv = ["trlc", *args]
        try:
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                try:
                    rv = trlc_main()
                except SystemExit as exc:
                    rv = exc.code
        finally:
            sys.argv = old_argv
        return rv, out.getvalue(), err.getvalue()

    def test_paths_from_file_are_excluded(self):
        list_file = self.write(
            "excludes.txt",
            "# a comment\n%s\n\n  %s  \n"
            % (
                os.path.join(self.tmp, "skip"),
                os.path.join(self.tmp, "baz.rsl"),
            ),
        )
        rv, out, _ = self.run_cli(
            "--exclude-from-file", list_file, "--show-file-list", self.tmp
        )
        self.assertEqual(rv, 0, out)
        self.assertIn("foo.rsl", out)
        self.assertNotIn("bar.rsl", out)
        self.assertNotIn("baz.rsl", out)

    def test_comments_and_blank_lines_are_ignored(self):
        list_file = self.write("excludes.txt", "# only a comment\n\n   \n")
        rv, _, _ = self.run_cli("--exclude-from-file", list_file, self.tmp)
        # Nothing excluded, so the invalid files are parsed and fail.
        self.assertEqual(rv, 1)

    def test_multiple_exclude_from_files(self):
        first = self.write("first.txt", os.path.join(self.tmp, "skip") + "\n")
        second = self.write("second.txt", os.path.join(self.tmp, "baz.rsl") + "\n")
        rv, out, _ = self.run_cli(
            "--exclude-from-file", first, "--exclude-from-file", second, self.tmp
        )
        self.assertEqual(rv, 0, out)

    def test_combined_with_exclude(self):
        list_file = self.write("excludes.txt", os.path.join(self.tmp, "skip") + "\n")
        rv, out, _ = self.run_cli(
            "--exclude-from-file",
            list_file,
            "--exclude",
            os.path.join(self.tmp, "baz.rsl"),
            self.tmp,
        )
        self.assertEqual(rv, 0, out)

    def test_include_directory_with_excluded_file_stops_cli(self):
        excluded_file = os.path.join(self.tmp, "skip", "bar.rsl")
        rv, out, err = self.run_cli(
            "--exclude",
            excluded_file,
            "-I",
            self.tmp,
            os.path.join(self.tmp, "foo.rsl"),
        )
        self.assertEqual(rv, 1)
        self.assertIn("include directory contains an excluded path", out + err)
        self.assertNotIn("Processed", out + err)

    def test_missing_list_file_is_an_error(self):
        rv, _, err = self.run_cli(
            "--exclude-from-file", os.path.join(self.tmp, "nope.txt"), self.tmp
        )
        self.assertEqual(rv, 2)
        self.assertIn("is not a file", err)

    def test_missing_listed_path_is_an_error(self):
        list_file = self.write("excludes.txt", os.path.join(self.tmp, "nope") + "\n")
        rv, _, err = self.run_cli("--exclude-from-file", list_file, self.tmp)
        self.assertEqual(rv, 2)
        self.assertIn("is not a file or directory", err)


if __name__ == "__main__":
    unittest.main()
