import os
import shutil
import tempfile
import unittest

from trlc.errors import Kind, Location, Message_Handler, TRLC_Error
from trlc.trlc import Source_Manager
from trlc import ast


class List_Handler(Message_Handler):
    def __init__(self):
        super().__init__()
        self.messages = []

    def emit(
        self, location, kind, message, fatal=True, extrainfo=None, category=None
    ):
        self.messages.append((kind, message))
        if fatal:
            raise TRLC_Error(location, kind, message)

    def has_error(self):
        return any(k in (Kind.SYS_ERROR, Kind.USER_ERROR) for k, _ in self.messages)

    def error_messages(self):
        return [m for k, m in self.messages if k in (Kind.SYS_ERROR, Kind.USER_ERROR)]

    def clear(self):
        self.messages = []


def make_source_manager(lint_mode=True):
    mh = List_Handler()
    return Source_Manager(mh=mh, lint_mode=lint_mode, error_recovery=False), mh


class Test_Nested_Packages(unittest.TestCase):
    """Tests for nested (dotted) package names, e.g. foo.bar."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp()

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def write(self, name, content):
        path = os.path.join(self.tmp, name)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
        return path

    # ------------------------------------------------------------------
    # Helper: run sm.process() and return the symbol table
    # ------------------------------------------------------------------
    def process(self, sm):
        return sm.process()

    # ------------------------------------------------------------------
    # Basic hierarchy tests
    # ------------------------------------------------------------------

    def test_basic_nested_package_declared(self):
        """Declaring foo and foo.bar succeeds; both are in the stab."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(self.write("foo.rsl", "package foo\ntype Base {}\n"))
        sm.register_rsl_file(
            self.write("foo_bar.rsl", "package foo.bar\ntype Item {}\n")
        )
        stab = self.process(sm)
        self.assertIsNotNone(stab)
        self.assertFalse(mh.has_error())
        foo = stab.lookup_assuming(mh, "foo", ast.Package)
        self.assertIsNotNone(foo)
        foo_bar = stab.lookup_assuming(mh, "foo.bar", ast.Package)
        self.assertIsNotNone(foo_bar)

    def test_parent_linked_to_child(self):
        """foo.bar.parent is foo, and foo.sub_packages contains foo.bar."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(self.write("foo.rsl", "package foo\ntype Base {}\n"))
        sm.register_rsl_file(
            self.write("foo_bar.rsl", "package foo.bar\ntype Item {}\n")
        )
        stab = self.process(sm)
        self.assertIsNotNone(stab)
        foo = stab.lookup_assuming(mh, "foo", ast.Package)
        foo_bar = stab.lookup_assuming(mh, "foo.bar", ast.Package)
        self.assertIs(foo_bar.parent, foo)
        child = foo.sub_packages.lookup_sub_package("bar")
        self.assertIs(child, foo_bar)

    def test_deep_hierarchy(self):
        """Three-level nesting a.b.c is supported."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(self.write("a.rsl", "package a\ntype Root {}\n"))
        sm.register_rsl_file(self.write("a_b.rsl", "package a.b\ntype Mid {}\n"))
        sm.register_rsl_file(self.write("a_b_c.rsl", "package a.b.c\ntype Leaf {}\n"))
        stab = self.process(sm)
        self.assertIsNotNone(stab)
        self.assertFalse(mh.has_error())
        a = stab.lookup_assuming(mh, "a", ast.Package)
        a_b = stab.lookup_assuming(mh, "a.b", ast.Package)
        a_b_c = stab.lookup_assuming(mh, "a.b.c", ast.Package)
        self.assertIs(a_b.parent, a)
        self.assertIs(a_b_c.parent, a_b)

    # ------------------------------------------------------------------
    # Parent declaration required
    # ------------------------------------------------------------------

    def test_missing_parent_errors(self):
        """Declaring foo.bar without declaring foo is an error."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(self.write("foo_bar.rsl", "package foo.bar\ntype T {}\n"))
        stab = self.process(sm)
        # Should produce an error about missing parent
        self.assertTrue(mh.has_error())
        msgs = mh.error_messages()
        self.assertTrue(
            any("parent package foo" in m for m in msgs),
            "Expected 'parent package foo' error, got: %s" % msgs,
        )

    # ------------------------------------------------------------------
    # Import and visibility
    # ------------------------------------------------------------------

    def test_import_nested_package(self):
        """A .trlc file can import a nested package and use its types."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(self.write("ns.rsl", "package ns\ntype Dummy {}\n"))
        sm.register_rsl_file(
            self.write("ns_pkg.rsl", "package ns.pkg\ntype Req {\n  x String\n}\n")
        )
        sm.register_trlc_file(
            self.write(
                "data.trlc",
                'package data\nimport ns.pkg\nns.pkg.Req R_001 { x = "hello" }\n',
            )
        )
        stab = self.process(sm)
        self.assertIsNotNone(stab)
        self.assertFalse(mh.has_error())

    def test_unimported_nested_package_error(self):
        """Using a nested package type without importing it is an error."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(self.write("foo.rsl", "package foo\ntype Base {}\n"))
        sm.register_rsl_file(
            self.write("foo_bar.rsl", "package foo.bar\ntype T {\n  x String\n}\n")
        )
        sm.register_trlc_file(
            self.write("data.trlc", 'package data\nfoo.bar.T OBJ { x = "y" }\n')
        )
        stab = self.process(sm)
        self.assertTrue(mh.has_error())
        msgs = mh.error_messages()
        self.assertTrue(
            any("must be imported" in m for m in msgs),
            "Expected 'must be imported' error, got: %s" % msgs,
        )

    def test_self_import_error(self):
        """A package importing itself is an error."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(self.write("foo.rsl", "package foo\ntype Dummy {}\n"))
        sm.register_rsl_file(
            self.write(
                "foo_bar.rsl", "package foo.bar\nimport foo.bar\ntype T { x String }\n"
            )
        )
        stab = self.process(sm)
        self.assertTrue(mh.has_error())
        msgs = mh.error_messages()
        self.assertTrue(
            any("cannot import itself" in m for m in msgs),
            "Expected 'cannot import itself' error, got: %s" % msgs,
        )

    # ------------------------------------------------------------------
    # Name collision
    # ------------------------------------------------------------------

    def test_collision_between_nested_packages(self):
        """foo.bar and Foo.Bar collide (sufficiently distinct check)."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(self.write("foo.rsl", "package foo\ntype D {}\n"))
        sm.register_rsl_file(self.write("Foo.rsl", "package Foo\ntype D {}\n"))
        sm.register_rsl_file(self.write("foo_bar.rsl", "package foo.bar\ntype T {}\n"))
        sm.register_rsl_file(self.write("Foo_Bar.rsl", "package Foo.Bar\ntype T {}\n"))
        stab = self.process(sm)
        self.assertTrue(mh.has_error())

    # ------------------------------------------------------------------
    # Wildcard imports (import foo.*)
    # ------------------------------------------------------------------

    def _warning_messages(self, mh):
        return [m for _k, m in mh.messages]

    def test_wildcard_import_exposes_subtree(self):
        """import com.shared.* exposes com.shared and its descendants."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(self.write("com.rsl", "package com\n"))
        sm.register_rsl_file(
            self.write("shared.rsl", "package com.shared\nenum U { a b }\n")
        )
        sm.register_rsl_file(
            self.write("si.rsl", "package com.shared.si\ntype F {\n  v Integer\n}\n")
        )
        sm.register_trlc_file(
            self.write(
                "data.trlc",
                "package app\nimport com.shared.*\n"
                "com.shared.si.F F_001 {\n  v = 1\n}\n",
            )
        )
        stab = self.process(sm)
        self.assertIsNotNone(stab)
        self.assertFalse(mh.has_error())

    def test_wildcard_empty_subtree(self):
        """import foo.* where foo has no children behaves like import foo."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write("foo.rsl", "package foo\ntype Req {\n  x String\n}\n")
        )
        sm.register_trlc_file(
            self.write(
                "data.trlc",
                'package app\nimport foo.*\nfoo.Req R_001 { x = "y" }\n',
            )
        )
        stab = self.process(sm)
        self.assertIsNotNone(stab)
        self.assertFalse(mh.has_error())

    def test_wildcard_undeclared_root_error(self):
        """import missing.* where missing is not declared is an error."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write("app.rsl", "package app\nimport missing.*\ntype T {}\n")
        )
        self.process(sm)
        self.assertTrue(mh.has_error())

    def test_wildcard_self_cover_allowed(self):
        """A wildcard whose root covers the current package is permitted."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(self.write("foo.rsl", "package foo\n"))
        sm.register_rsl_file(
            self.write("foo_bar.rsl", "package foo.bar\nimport foo.*\ntype T {}\n")
        )
        self.process(sm)
        self.assertFalse(
            any("cannot import itself" in m for m in self._warning_messages(mh)),
            "Wildcard self-cover must not be a self-import error",
        )

    def test_wildcard_self_cover_no_self_cycle(self):
        """A self-covering wildcard that is used must not create a spurious
        circular dependency on the package itself."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(self.write("foo.rsl", "package foo\n"))
        sm.register_rsl_file(
            self.write("foo_baz.rsl", "package foo.baz\nenum Color { a b }\n")
        )
        sm.register_rsl_file(
            self.write(
                "foo_bar.rsl",
                "package foo.bar\nimport foo.*\ntype R {\n  c foo.baz.Color\n}\n",
            )
        )
        self.process(sm)
        self.assertFalse(
            any("circular" in m for m in mh.error_messages()),
            "Self-covering wildcard must not produce a circular dependency, "
            "got: %s" % mh.error_messages(),
        )

    def test_wildcard_unused_lint(self):
        """An unused wildcard import is flagged by the linter."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(self.write("foo.rsl", "package foo\n"))
        sm.register_rsl_file(self.write("sub.rsl", "package sub\ntype T {}\n"))
        sm.register_rsl_file(
            self.write("foobar.rsl", "package foo.bar\nimport sub.*\ntype R {}\n")
        )
        self.process(sm)
        self.assertTrue(
            any(
                "unused wildcard import sub.*" in m
                for m in self._warning_messages(mh)
            ),
            "Expected unused wildcard warning, got: %s"
            % self._warning_messages(mh),
        )

    def test_wildcard_redundant_lint(self):
        """An explicit import covered by a wildcard is flagged as redundant."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(self.write("foo.rsl", "package foo\n"))
        sm.register_rsl_file(self.write("sub.rsl", "package sub\n"))
        sm.register_rsl_file(
            self.write("subdeep.rsl", "package sub.deep\ntype U {\n  v Integer\n}\n")
        )
        sm.register_rsl_file(
            self.write(
                "foobar.rsl",
                "package foo.bar\nimport sub.*\nimport sub.deep\n"
                "type R {\n  x sub.deep.U\n}\n",
            )
        )
        self.process(sm)
        self.assertTrue(
            any("redundant import sub.deep" in m for m in self._warning_messages(mh)),
            "Expected redundant import warning, got: %s"
            % self._warning_messages(mh),
        )

    # ------------------------------------------------------------------
    # Sub-package vs member distinctness (S12)
    # ------------------------------------------------------------------

    def test_subpackage_member_collision(self):
        """A sub-package leaf clashing with a parent member is an error."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write("foo.rsl", "package foo\ntype Bar {\n  v Integer\n}\n")
        )
        sm.register_rsl_file(self.write("foo_bar.rsl", "package foo.Bar\ntype W {}\n"))
        self.process(sm)
        self.assertTrue(mh.has_error())
        self.assertTrue(
            any("clashes with a type or object" in m for m in mh.error_messages()),
            "Expected sub-package/member clash error, got: %s"
            % mh.error_messages(),
        )

    def test_shadow_resolve_type_and_subpackage(self):
        """foo.T and foo.bar.T coexist and both resolve correctly."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write("foo.rsl", "package foo\ntype T {\n  a Integer\n}\n")
        )
        sm.register_rsl_file(
            self.write("foo_bar.rsl", "package foo.bar\ntype T {\n  b Integer\n}\n")
        )
        sm.register_trlc_file(
            self.write(
                "data.trlc",
                "package app\nimport foo\nimport foo.bar\n"
                "foo.T X_001 {\n  a = 1\n}\n"
                "foo.bar.T Y_001 {\n  b = 2\n}\n",
            )
        )
        stab = self.process(sm)
        self.assertIsNotNone(stab)
        self.assertFalse(mh.has_error())


class Test_Symbol_Table_Nested(unittest.TestCase):
    """Tests for Symbol_Table methods added for nested packages."""

    def setUp(self):
        self.mh = List_Handler()
        self.stab = ast.Symbol_Table.create_global_table(self.mh)

    def test_lookup_sub_package_returns_none_for_missing(self):
        result = self.stab.lookup_sub_package("nonexistent")
        self.assertIsNone(result)

    def test_register_with_key_and_lookup(self):
        loc = Location("test.rsl")
        pkg = ast.Package(
            name="foo.bar", location=loc, builtin_stab=self.stab, declared_late=False
        )
        # Register under leaf key "bar"
        sub = ast.Symbol_Table()
        sub.register_with_key(self.mh, pkg, "bar")
        result = sub.lookup_sub_package("bar")
        self.assertIs(result, pkg)

    def test_register_with_key_duplicate_raises(self):
        loc = Location("test.rsl")
        pkg1 = ast.Package(
            name="foo.bar", location=loc, builtin_stab=self.stab, declared_late=False
        )
        pkg2 = ast.Package(
            name="foo.bar", location=loc, builtin_stab=self.stab, declared_late=False
        )
        sub = ast.Symbol_Table()
        sub.register_with_key(self.mh, pkg1, "bar")
        with self.assertRaises(TRLC_Error):
            sub.register_with_key(self.mh, pkg2, "bar")


if __name__ == "__main__":
    unittest.main()
