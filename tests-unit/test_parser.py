import os
import shutil
import tempfile
import unittest

from trlc import ast
from trlc.errors import Kind, Location, Message_Handler, TRLC_Error
from trlc.trlc import Source_Manager


class List_Handler(Message_Handler):
    def __init__(self):
        super().__init__()
        self.messages = []
        self.explanations = []

    def emit(self, location, kind, message, fatal=True, extrainfo=None, category=None):
        self.messages.append((kind, message))
        self.explanations.append(extrainfo)
        if fatal:
            raise TRLC_Error(location, kind, message)

    def has_error(self):
        return any(k in (Kind.SYS_ERROR, Kind.USER_ERROR) for k, _ in self.messages)

    def error_messages(self):
        return [m for k, m in self.messages if k in (Kind.SYS_ERROR, Kind.USER_ERROR)]


def make_source_manager(lint_mode=True):
    mh = List_Handler()
    return Source_Manager(mh=mh, lint_mode=lint_mode, error_recovery=False), mh


class Test_Parser_Forward_References(unittest.TestCase):
    """Parser tests for forward references resolved later in the same file."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp()

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def write(self, name, content):
        path = os.path.join(self.tmp, name)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
        return path

    def process(self, sm):
        return sm.process()

    def test_inheritance_requires_parent_declared_first(self):
        cases = {
            "later": ("type Child extends Parent {}\ntype Parent {}\n", "Parent"),
            "forward_reference": (
                "type User { p Parent }\ntype Child extends Parent {}\ntype Parent {}\n",
                "Parent",
            ),
            "missing": ("type Child extends Parent {}\n", "Parent"),
            "qualified_later": (
                "type Child extends demo.Parent {}\ntype Parent {}\n",
                "Parent",
            ),
            "qualified_forward_reference": (
                "type User { p Parent }\n"
                "type Child extends demo.Parent {}\ntype Parent {}\n",
                "Parent",
            ),
        }
        for case, (declarations, name) in cases.items():
            for lint_mode in (True, False):
                with self.subTest(case=case, lint_mode=lint_mode):
                    sm, mh = make_source_manager(lint_mode=lint_mode)
                    sm.register_rsl_file(
                        self.write("inheritance.rsl", "package demo\n" + declarations)
                    )
                    self.assertIsNone(self.process(sm))
                    # Later errors may follow for leftover forward stubs.
                    self.assertEqual(
                        mh.error_messages()[0],
                        f"cannot extend {name} before it is declared",
                    )
                    self.assertEqual(
                        mh.explanations[0],
                        f"{name} is declared later or not at all; "
                        "declare it before the derived type",
                    )

    def test_inheritance_from_unknown_package_is_unknown_symbol(self):
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "inheritance.rsl",
                "package demo\ntype Child extends Missing.Parent {}\n",
            )
        )
        self.assertIsNone(self.process(sm))
        self.assertEqual(mh.error_messages(), ["unknown symbol Missing"])

    def test_inheritance_accepts_parent_from_imported_package(self):
        sm, mh = make_source_manager()
        sm.register_rsl_file(self.write("base.rsl", "package base\ntype Parent {}\n"))
        sm.register_rsl_file(
            self.write(
                "derived.rsl",
                "package derived\nimport base\ntype Child extends base.Parent {}\n",
            )
        )
        self.assertIsNotNone(self.process(sm))
        self.assertFalse(mh.has_error())

    def test_inheritance_accepts_qualified_parent_declared_first(self):
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "inheritance.rsl",
                "package demo\ntype Parent {}\ntype Child extends demo.Parent {}\n",
            )
        )
        self.assertIsNotNone(self.process(sm))
        self.assertFalse(mh.has_error())

    def test_inheritance_accepts_parent_declared_first(self):
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "inheritance.rsl",
                "package demo\ntype Parent {}\ntype Child extends Parent {}\n",
            )
        )
        self.assertIsNotNone(self.process(sm))
        self.assertFalse(mh.has_error())

    def test_record_type_forward_reference(self):
        """A record type may be referenced before its later declaration in the same file."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "forward.rsl",
                "package demo\ntype A {\n  b B\n}\ntype B {\n  a A\n}\n",
            )
        )
        stab = self.process(sm)
        self.assertIsNotNone(stab)
        self.assertFalse(mh.has_error())
        pkg = stab.lookup_assuming(mh, "demo", ast.Package)
        a = pkg.symbols.lookup_assuming(mh, "A", ast.Record_Type)
        b = pkg.symbols.lookup_assuming(mh, "B", ast.Record_Type)
        self.assertIsNotNone(a)
        self.assertIsNotNone(b)
        self.assertIs(a.components.lookup_assuming(mh, "b").n_typ, b)
        self.assertIs(b.components.lookup_assuming(mh, "a").n_typ, a)

    def test_union_accepts_previously_declared_tuple_and_record(self):
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "union_tuple.rsl",
                "package demo\n"
                "tuple RequirementId {\n"
                "  item Integer\n"
                "  separator @\n"
                "  version Integer\n"
                "}\n"
                "tuple Coordinate {\n"
                "  item Integer\n"
                "  version Integer\n"
                "}\n"
                "type Record_A {\n"
                "  version Integer\n"
                "}\n"
                "type A {\n"
                "  choice [RequirementId, Coordinate, Record_A]\n"
                "}\n"
                'checks A {\n  choice.version >= 0, warning "negative version"\n}\n',
            )
        )
        sm.register_trlc_file(
            self.write(
                "union_tuple.trlc",
                "package demo\n"
                "Record_A record_value { version = 3 }\n"
                "A tuple_choice { choice = 1@2 }\n"
                "A generic_choice { choice = (4, 5) }\n"
                "A record_choice { choice = record_value }\n",
            )
        )

        stab = self.process(sm)
        self.assertIsNotNone(stab)
        self.assertFalse(mh.has_error(), mh.error_messages())

        pkg = stab.lookup_assuming(mh, "demo", ast.Package)
        tuple_type = pkg.symbols.lookup_assuming(mh, "RequirementId", ast.Tuple_Type)
        coordinate_type = pkg.symbols.lookup_assuming(mh, "Coordinate", ast.Tuple_Type)
        tuple_choice = pkg.symbols.lookup_assuming(
            mh, "tuple_choice", ast.Record_Object
        )
        generic_choice = pkg.symbols.lookup_assuming(
            mh, "generic_choice", ast.Record_Object
        )
        record_choice = pkg.symbols.lookup_assuming(
            mh, "record_choice", ast.Record_Object
        )
        record_value = pkg.symbols.lookup_assuming(
            mh, "record_value", ast.Record_Object
        )
        tuple_value = tuple_choice.field["choice"]
        record_reference = record_choice.field["choice"]

        self.assertIsInstance(tuple_value, ast.Tuple_Aggregate)
        self.assertIs(tuple_value.typ, tuple_type)
        generic_tuple = generic_choice.field["choice"]
        self.assertIsInstance(generic_tuple, ast.Tuple_Aggregate)
        self.assertIs(generic_tuple.typ, coordinate_type)
        self.assertIsInstance(record_reference, ast.Record_Reference)
        self.assertIs(record_reference.target, record_value)

    def test_tuple_union_member_must_be_declared_first(self):
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "forward_union_tuple.rsl",
                "package demo\n"
                "type Record_A {}\n"
                "type A { choice [Later_Tuple, Record_A] }\n"
                "tuple Later_Tuple { item Integer }\n",
            )
        )

        stab = self.process(sm)
        self.assertIsNone(stab)
        self.assertTrue(
            any(
                "Tuple_Type Later_Tuple must be declared before its use in a union"
                in message
                for message in mh.error_messages()
            )
        )

    def test_union_keeps_forward_record_member_support(self):
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "forward_union_record.rsl",
                "package demo\n"
                "tuple RequirementId { item Integer }\n"
                "type A { choice [Record_A, RequirementId] }\n"
                "type Record_A { version Integer }\n",
            )
        )
        sm.register_trlc_file(
            self.write(
                "forward_union_record.trlc",
                "package demo\n"
                "Record_A record_value { version = 3 }\n"
                "A choice_value { choice = record_value }\n",
            )
        )

        stab = self.process(sm)
        self.assertIsNotNone(stab)
        self.assertFalse(mh.has_error(), mh.error_messages())
        pkg = stab.lookup_assuming(mh, "demo", ast.Package)
        union = pkg.symbols.lookup_assuming(mh, "A", ast.Record_Type)
        union_type = union.components.lookup_assuming(mh, "choice").n_typ
        self.assertIsInstance(union_type, ast.Union_Type)
        self.assertIsInstance(union_type.types[0], ast.Record_Type)

    def test_tuple_type_forward_reference(self):
        """A tuple type may be referenced before its later declaration in the same file."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "forward_tuple.rsl",
                "package demo\nabstract type ADBase { description String }\n"
                "type ComponentRequirement extends ADBase {\n"
                "  derived_from ComponentRequirementId [0 .. *]\n}\n"
                "tuple ComponentRequirementId {\n"
                "  item      ComponentRequirement\n"
                "  separator @\n"
                "  version   Integer\n}\n",
            )
        )
        stab = self.process(sm)
        self.assertIsNotNone(stab)
        self.assertFalse(mh.has_error())
        pkg = stab.lookup_assuming(mh, "demo", ast.Package)
        tuple_type = pkg.symbols.lookup_assuming(
            mh, "ComponentRequirementId", ast.Tuple_Type
        )
        self.assertIsNotNone(tuple_type)
        self.assertIs(
            tuple_type.components.lookup_assuming(mh, "item").n_typ,
            pkg.symbols.lookup_assuming(mh, "ComponentRequirement", ast.Record_Type),
        )

    def test_union_type_forward_reference(self):
        """A union member may be a forward-declared record type in the same file."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "forward_union.rsl",
                "package demo\ntype A {\n  b [B]\n}\ntype B {\n  a A\n}\n",
            )
        )
        stab = self.process(sm)
        self.assertIsNotNone(stab)
        self.assertFalse(mh.has_error())
        pkg = stab.lookup_assuming(mh, "demo", ast.Package)
        a = pkg.symbols.lookup_assuming(mh, "A", ast.Record_Type)
        b = pkg.symbols.lookup_assuming(mh, "B", ast.Record_Type)
        self.assertIsNotNone(a)
        self.assertIsNotNone(b)
        field_type = a.components.lookup_assuming(mh, "b").n_typ
        self.assertIsInstance(field_type, ast.Union_Type)
        self.assertEqual(len(field_type.types), 1)
        self.assertIs(field_type.types[0], b)

    def test_union_member_must_be_record_type(self):
        """Non-record members in a union are rejected without crashing."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "invalid_union_member.rsl",
                "package demo\ntype A {\n  b [B]\n}\nenum B {\n  X\n}\n",
            )
        )
        stab = self.process(sm)
        self.assertIsNone(stab)
        self.assertTrue(any("is not a Record_Type" in msg for _, msg in mh.messages))

    def test_union_member_cannot_forward_reference_enum(self):
        """A later enum declaration may not be used as a union member."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "forward_union_enum.rsl",
                "package demo\n"
                "type A {\n"
                "  b [Severity]\n"
                "}\n"
                "enum Severity {\n"
                "  HIGH\n"
                "  LOW\n"
                "}\n",
            )
        )
        stab = self.process(sm)
        self.assertIsNone(stab)
        self.assertTrue(any("is not a Record_Type" in msg for _, msg in mh.messages))

    def test_union_forward_non_record_is_error_without_lint(self):
        """--no-lint must not make an enum or tuple union member valid."""
        cases = {
            "Enumeration_Type": "enum Severity {\n  HIGH\n}\n",
            "Tuple_Type": "tuple Severity {\n  x Integer\n  y Integer\n}\n",
        }
        for kind, declaration in cases.items():
            for lint_mode in (True, False):
                with self.subTest(kind=kind, lint_mode=lint_mode):
                    sm, mh = make_source_manager(lint_mode=lint_mode)
                    sm.register_rsl_file(
                        self.write(
                            "forward_union_no_lint.rsl",
                            "package demo\ntype A {\n  b [Severity]\n}\n" + declaration,
                        )
                    )
                    sm.process()
                    expected_message = (
                        "Tuple_Type Severity must be declared before its use in a union"
                        if kind == "Tuple_Type"
                        else f"{kind} Severity is not a Record_Type"
                    )
                    self.assertEqual(
                        mh.error_messages(),
                        [expected_message],
                    )

    def test_union_forward_enum_field_access_does_not_crash(self):
        """Field access on a union whose member later became an enum is an error."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "forward_union_enum_access.rsl",
                "package demo\n"
                "type A {\n  choice [Severity]\n}\n"
                "enum Severity {\n  HIGH\n}\n"
                'checks A {\n  choice.foo == 1, "bad"\n}\n',
            )
        )
        stab = self.process(sm)
        self.assertIsNone(stab)
        self.assertIn(
            "Enumeration_Type Severity is not a Record_Type",
            mh.error_messages(),
        )

    def test_union_forward_enum_equality_reports_root_cause(self):
        """Comparing a union whose member later became an enum names the enum."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "forward_union_enum_eq.rsl",
                "package demo\n"
                "type A {\n  choice [Severity]\n}\n"
                "enum Severity {\n  HIGH\n}\n"
                'checks A {\n  choice == choice, "bad"\n}\n',
            )
        )
        stab = self.process(sm)
        self.assertIsNone(stab)
        self.assertEqual(
            mh.error_messages(),
            ["Enumeration_Type Severity is not a Record_Type"],
        )

    def test_tuple_field_cannot_forward_reference_enum(self):
        """Tuple fields may not reference an enum declared later in the same file."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "forward_tuple_enum.rsl",
                "package demo\n"
                "tuple RequirementId {\n"
                "  item Severity\n"
                "  separator @\n"
                "  version Integer\n"
                "}\n"
                "enum Severity {\n"
                "  HIGH\n"
                "  LOW\n"
                "}\n",
            )
        )
        stab = self.process(sm)
        self.assertIsNotNone(stab)
        self.assertTrue(mh.error_messages())
        self.assertIn(
            "unknown symbol Severity",
            "\n".join(mh.error_messages()),
        )

    def test_mutually_recursive_tuples_are_rejected(self):
        """Tuples may not form a cycle via a forward reference to a later tuple."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "mutual_tuples.rsl",
                "package demo\n"
                "tuple A {\n  item B\n  version Integer\n}\n"
                "tuple B {\n  item A\n  version Integer\n}\n",
            )
        )
        stab = self.process(sm)
        self.assertIsNone(stab)
        self.assertEqual(mh.error_messages(), ["unknown symbol B"])

    def test_tuple_type_self_reference_is_rejected(self):
        """A tuple may not reference itself while it is still being declared."""
        sm, mh = make_source_manager()
        sm.register_rsl_file(
            self.write(
                "forward_tuple_self.rsl",
                "package demo\ntuple T {\n  item T\n}\n",
            )
        )
        stab = self.process(sm)
        self.assertIsNone(stab)
        self.assertTrue(mh.error_messages())
        self.assertIn(
            "unknown symbol T",
            "\n".join(mh.error_messages()),
        )


if __name__ == "__main__":
    unittest.main()
