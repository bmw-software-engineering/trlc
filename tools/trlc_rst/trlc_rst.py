import argparse
import logging
import os
import re
import sys

import trlc.ast
from trlc.errors import Message_Handler
from trlc.trlc import Source_Manager

from bigtree import Node, preorder_iter

logger = logging.getLogger(__name__)

RST_HEADLINE_SEPARATORS = ("=", "-", "^", "'")
_MARKUP_REF_RE = re.compile(r"\[\[([^\]]+)\]\]")
_RST_DIRECTIVE_RE = re.compile(r"^\.\. [a-zA-Z][\w-]*::")
_MD_IMAGE_RE = re.compile(r"!\[([^\]]*)\]\(([^\)]+)\)")
_DEFAULT_FIELDS = ["description"]


class TRLCParseError(Exception):
    """Exception raised when TRLC parsing fails."""

    pass


class TRLCRST:
    """Renders TRLC files to reStructuredText format."""

    def __init__(
        self,
        input_directory: str | None = None,
        source_files: list[str] | None = None,
        dep_files: list[str] | None = None,
    ):
        """Initialize the renderer.

        Args:
            input_directory: Directory to scan for TRLC files.  When given,
                ``Source_Manager.register_directory`` is used.  ``source_files``
                may optionally restrict which record objects are rendered.
            source_files: Explicit list of .trlc files whose record objects
                should be rendered.  Files not in this list are still parsed
                for dependency resolution but are not included in the output.
                When *input_directory* is ``None`` these files are registered
                directly via ``register_file``.
            dep_files: Additional files (*.rsl specs and dependency *.trlc
                files) to register for dependency resolution only.  Only used
                when *input_directory* is ``None``.
        """
        self.input_directory = input_directory
        self._source_files = source_files
        self._dep_files = dep_files
        self._symbols = None
        self._requirements_tree = None

    @staticmethod
    def _default_label(field_name: str) -> str:
        """Derive a human-readable column/field label from a field name."""
        return field_name.replace("_", " ").strip().title()

    @classmethod
    def _normalize_fields(cls, fields: list[str] | dict[str, str]) -> list[tuple[str, str]]:
        """Convert a field spec to ``[(field_name, label), ...]``.

        Accepts:
        - ``list[str]``: labels are derived automatically from field names.
        - ``dict[str, str]``: maps ``{field_name: label}`` (custom labels).
        """
        if isinstance(fields, dict):
            return list(fields.items())
        return [(f, cls._default_label(f)) for f in fields]

    def _resolve_source_files(self) -> set[str] | None:
        """Resolve source file paths to absolute paths for filtering.

        Returns:
            Set of absolute file paths, or None if all files should be rendered.
        """
        if self._source_files is None:
            return None
        return {os.path.abspath(f) for f in self._source_files}

    def parse_trlc_files(self) -> None:
        """Parse TRLC files.

        When *input_directory* is set the directory is scanned via
        ``register_directory``.  Otherwise every file in *dep_files* and
        *source_files* is registered individually via ``register_file``.

        Idempotent: if files have already been parsed this call is a no-op.
        """
        if self._symbols is not None:
            return
        message_handler = Message_Handler()
        source_manager = Source_Manager(message_handler)

        if self.input_directory is not None:
            source_manager.register_directory(self.input_directory)
        else:
            registered: set[str] = set()
            for f in self._source_files or []:
                source_manager.register_file(f)
                registered.add(os.path.abspath(f))
            for f in self._dep_files or []:
                if os.path.abspath(f) not in registered:
                    source_manager.register_file(f)
                    registered.add(os.path.abspath(f))

        symbols = source_manager.process()
        if symbols is None:
            # TRLC Message_Handler has already printed detailed diagnostics to stderr
            raise TRLCParseError(
                "Failed to parse TRLC files. See error messages below for details."
            )

        self._symbols = symbols

    def convert_symbols_to_tree(self, records: set[str] | None = None) -> None:
        """Convert parsed symbols to a hierarchical tree structure.

        Tree Construction Algorithm:
        For each TRLC requirement object:
        1. Build a temporary tree containing the section hierarchy path
           (e.g., root -> "ISO 26262" -> "Management" -> "SafetyCulture")
        2. Traverse this temporary tree from root to leaf using preorder iteration
        3. For each node in the path:
           - Check if a node with the same name already exists in the main tree
           - If found: Navigate down to that existing node (reuse structure)
           - If not found: Append the entire remaining subtree and stop

        Example: If two requirements share sections "ISO 26262" -> "Management",
        those sections are created once and both requirements become children.

        Args:
            records: Optional set of fully-qualified names to include.
        """
        requirements_root = Node("root")
        obj: trlc.ast.Record_Object
        for obj in self._iter_filtered_objects(records):
            parent_root = Node("root")
            parent_tree = self._build_parent_tree(obj.section, parent_root)
            # Store the TRLC object in the node so we can access its attributes later
            parent_tree.append(Node(obj.fully_qualified_name(), trlc_obj=obj))

            # Merge both trees
            to_tree = requirements_root
            for from_node in preorder_iter(parent_root):
                if from_node.is_root:
                    continue

                found = False
                for to_node in to_tree.children:
                    if to_node.name == from_node.name:
                        found = True
                        to_tree = to_node
                        break

                if found is True:
                    continue

                to_tree.append(from_node)
                break

        self._requirements_tree = requirements_root

    def render_to_file(
        self,
        output_path: str,
        title: str = "Requirements",
        fields: list[str] | None = None,
    ) -> None:
        """Render the requirements tree to a reStructuredText file.

        Args:
            output_path: Path of the RST file to write.
            title: Section title written at the top of the file.
                   Pass an empty string to omit the title entirely
                   (useful when the output is ``.. include::``d inside an
                   already-titled section).
            fields: Field spec (see :meth:`render`).  Defaults to
                ``["description"]``.
        """
        if self._requirements_tree is None:
            raise ValueError(
                "Requirements tree not built. Call convert_symbols_to_tree() first."
            )

        normalized = self._normalize_fields(fields if fields is not None else _DEFAULT_FIELDS)

        with open(output_path, "w", newline="", encoding="utf-8") as file:
            if title:
                file.write(f"{title}\n")
                file.write(f"{RST_HEADLINE_SEPARATORS[0] * len(title)}\n")

            # When the title is omitted the top-level section nodes (depth 2)
            # are promoted: depth 2 -> key 1 ("="), depth 3 -> key 2 ("-"), etc.
            depth_offset = 1 if not title else 0

            for node in preorder_iter(self._requirements_tree):
                if node.is_root:
                    continue

                if not node.is_leaf:
                    file.write(f"{node.name}\n")
                    lookup = node.depth - depth_offset
                    if 0 < lookup <= len(RST_HEADLINE_SEPARATORS):
                        separator_char = RST_HEADLINE_SEPARATORS[lookup - 1]
                    else:
                        logger.warning(
                            "Section '%s' at depth %d exceeds max RST heading depth, "
                            'falling back to "\'" separator',
                            node.name,
                            node.depth,
                        )
                        separator_char = "'"
                    file.write(f"{separator_char * len(node.name)}\n")

                else:
                    trlc_obj = getattr(node, "trlc_obj", None)
                    file.write(
                        "\n".join(self._render_record_block(node.name, trlc_obj, normalized))
                    )
                    file.write("\n")

    @staticmethod
    def _is_markup_field(trlc_obj, field_name: str) -> bool:
        """Return True when *field_name* is a ``Markup_String`` field."""
        if trlc_obj is None:
            return False
        field_node = trlc_obj.field.get(field_name)
        return isinstance(field_node, trlc.ast.String_Literal) and field_node.has_references

    def _field_value(self, trlc_obj, field_name: str) -> str | None:
        """Return the rendered value of *field_name* on *trlc_obj*.

        ``Markup_String`` fields get ``[[...]]`` markup-reference resolution;
        all other fields are read from ``to_python_dict()`` (enums become their
        literal name).  Returns ``None`` when the field is absent or ``None``.
        """
        if trlc_obj is None:
            return None
        field_node = trlc_obj.field.get(field_name)
        if isinstance(field_node, trlc.ast.String_Literal) and field_node.has_references:
            return TRLCRST._resolve_markup_references(
                field_node.value, field_node.references
            )
        return trlc_obj.to_python_dict().get(field_name)

    def _render_record_block(self, fqn: str, trlc_obj, fields: list[tuple[str, str]]) -> list:
        """Render one record as a ``requirement:definition`` directive block.

        ``Markup_String`` fields are rendered as preprocessed prose paragraphs.
        All other fields are rendered as ``:Label: value`` field-list entries.

        Returns a list of RST lines (with a trailing blank line).
        """
        lines = [f".. requirement:definition:: {fqn}", ""]

        field_list = []
        block_values = []
        for field_name, label in fields:
            value = self._field_value(trlc_obj, field_name)
            if value is None or value == "":
                continue
            if self._is_markup_field(trlc_obj, field_name):
                block_values.append(value)
            else:
                field_list.append((label, value))

        for label, value in field_list:
            lines.append(f":{label}: {value}")
        if field_list:
            lines.append("")
        for value in block_values:
            lines.append(self._preprocess_description(value))
            lines.append("")
        if not field_list and not block_values:
            lines.append("")
        return lines

    def _iter_filtered_objects(self, records: set[str] | None = None):
        """Yield record objects honouring the source-file and fqn filters.

        Args:
            records: Optional set of fully-qualified names; when given, only
                records in the set are yielded (applied on top of the
                source-file filter).
        """
        if self._symbols is None:
            raise ValueError("Symbols not parsed. Call parse_trlc_files() first.")
        source_file_set = self._resolve_source_files()
        for obj in self._symbols.iter_record_objects():
            if source_file_set is not None:
                if os.path.abspath(obj.location.file_name) not in source_file_set:
                    continue
            if records is not None and obj.fully_qualified_name() not in records:
                continue
            yield obj

    def _objects_by_fqn(self, records: set[str] | None = None) -> dict:
        """Return ``{fully_qualified_name: trlc_obj}`` for all filtered records."""
        return {o.fully_qualified_name(): o for o in self._iter_filtered_objects(records)}

    def objects_by_fqn(self, records: set[str] | None = None) -> dict:
        """Public access to ``{fqn: trlc_obj}`` for callers needing raw TRLC objects."""
        return self._objects_by_fqn(records)

    def field_value_for(
        self,
        fqn: str,
        field_name: str,
        records: set[str] | None = None,
    ) -> str | None:
        """Return the rendered value of *field_name* for the record *fqn*.

        For string fields (both plain ``String`` and ``Markup_String``),
        applies Markdown/RST preprocessing and returns a flush-left string
        with no directive-body indent, so the caller can embed it freely
        (e.g. inside a sphinx-design ``dropdown``).
        ``Markup_String`` fields additionally get ``[[...]]`` reference
        resolution.  Non-string fields are returned as their plain string
        representation.

        Args:
            fqn: Fully-qualified record name.
            field_name: Name of the field to render.
            records: Optional FQN filter (same semantics as in render methods).

        Returns:
            Rendered string, or ``None`` if the record or field is absent.
        """
        obj = self._objects_by_fqn(records).get(fqn)
        if obj is None:
            return None
        value = self._field_value(obj, field_name)
        if not value:
            return None
        field_node = obj.field.get(field_name)
        if isinstance(field_node, trlc.ast.String_Literal):
            return self._preprocess_description(value, indent=0)
        return value

    def render_records_to_string(
        self,
        fields: list[str] | None = None,
        fqns: list[str] | None = None,
        records: set[str] | None = None,
    ) -> str:
        """Render selected records to an RST string (no section headings).

        Args:
            fields: Field names to render.  Defaults to ``["description"]``.
            fqns: Ordered list of fully-qualified record names to render.
                ``None`` renders every record passing the source-file and
                *records* filters, in parse order.  Unknown names are skipped.
            records: Optional set of fully-qualified names to include
                (additional filter on top of the source-file filter).

        Returns:
            RST string ending with a newline.
        """
        normalized = self._normalize_fields(fields if fields is not None else _DEFAULT_FIELDS)
        obj_map = self._objects_by_fqn(records)
        if fqns is None:
            objs = list(self._iter_filtered_objects(records))
        else:
            objs = [obj_map[f] for f in fqns if f in obj_map]

        lines = []
        for obj in objs:
            lines += self._render_record_block(
                obj.fully_qualified_name(), obj, normalized
            )
        return "\n".join(lines) + "\n"

    def render_table_to_string(
        self,
        columns: list[str] | dict[str, str],
        fqns: list[str] | None = None,
        name_header: str = "Name",
        link_fn=None,
        records: set[str] | None = None,
    ) -> str:
        """Render a summary ``.. list-table::`` with one row per record.

        Args:
            columns: Field names to use as columns after the leading name
                column.  Labels are auto-derived from the field names.
            fqns: Ordered list of fully-qualified record names (rows).  When
                ``None`` every record passing the source-file and *records*
                filters is included in parse order.
            name_header: Header label for the leading name column.
            link_fn: Optional ``(fqn, name) -> str`` returning the RST text for
                the name cell (e.g. a ``:ref:`` cross-reference).  Defaults to
                the bare record name.
            records: Optional set of fully-qualified names to include.

        Returns:
            RST string ending with a newline.
        """
        normalized = self._normalize_fields(columns)
        obj_map = self._objects_by_fqn(records)
        if fqns is None:
            objs = [(o.fully_qualified_name(), o) for o in self._iter_filtered_objects(records)]
        else:
            objs = [(f, obj_map[f]) for f in fqns if f in obj_map]

        lines = [".. list-table::", "   :header-rows: 1", ""]
        header = [name_header] + [label for _, label in normalized]
        lines.append(f"   * - {header[0]}")
        for head in header[1:]:
            lines.append(f"     - {head}")
        for fqn, obj in objs:
            name = obj.name if hasattr(obj, "name") else fqn
            cell = link_fn(fqn, name) if link_fn is not None else name
            lines.append(f"   * - {cell}")
            for field_name, _ in normalized:
                value = self._field_value(obj, field_name)
                lines.append(f"     - {'' if value is None else value}")
        lines.append("")
        return "\n".join(lines) + "\n"

    @staticmethod
    def _resolve_markup_references(raw_value: str, references: list) -> str:
        """Replace [[...]] markup references with RST cross-reference roles.

        Each ``[[name]]`` or ``[[Package.name]]`` in *raw_value* is converted
        to a ``:requirement:upstream-ref:`FQN``` RST role using the
        fully-qualified name resolved from the supplied *references* list.
        Comma-separated references inside one ``[[...]]`` block
        (e.g. ``[[A, B]]``) are expanded to individual roles joined by
        a comma.
        """
        if not references or "[[" not in raw_value:
            return raw_value

        ref_iter = iter(references)

        def _replace(match):
            inner = match.group(1)
            count = inner.count(",") + 1
            parts = []
            for _ in range(count):
                try:
                    ref = next(ref_iter)
                except StopIteration:
                    break
                if ref.target is not None:
                    fqn = ref.target.fully_qualified_name()
                    short = ref.target.name
                    parts.append(
                        f":requirement:upstream-ref:`{short} <{fqn}>`"
                    )
                else:
                    parts.append(match.group(0))
            return ", ".join(parts)

        return _MARKUP_REF_RE.sub(_replace, raw_value)

    @staticmethod
    def _preprocess_description(description: str, indent: int = 3) -> str:
        """Preprocess a description for proper reStructuredText formatting.

        Supported RST formatting in descriptions:
        - **Bold text**: **text**
        - *Italic text*: *text*
        - Inline code: ``code``
        - Hyperlinks: [text](url) converted to `text <url>`_
        - Images: ![alt](path) converted to ``.. image:: path`` (with ``:alt:`` when alt is non-empty)
        - Code blocks: Line ending with :: followed by indented content
        - RST directives: ``.. image::``, ``.. figure::``, etc. with options
        - Bullet lists: Lines starting with -
        - Numbered lists: Lines starting with 1., 2., etc.
        - Soft wraps: Consecutive non-empty lines are joined into a single
          RST paragraph; insert a blank line to start a new paragraph."""
        if not description:
            return description

        # Convert Markdown-style images ![alt](path) to RST ``.. image::`` directives.
        # Must run before the link regex so that [alt](path) inside ![alt](path)
        # is not matched first.
        def _md_image_sub(m):
            alt, path = m.group(1), m.group(2)
            return f".. image:: {path}\n   :alt: {alt}" if alt else f".. image:: {path}"

        description = _MD_IMAGE_RE.sub(_md_image_sub, description)

        # Convert Markdown-style links [text](url) to RST-style `text <url>`_
        description = re.sub(r"\[([^\]]+)\]\(([^\)]+)\)", r"`\1 <\2>`_", description)

        lines = description.split("\n")
        processed_lines = []
        prev_was_list_item = False
        in_code_block = False
        code_block_base_indent = 0
        in_directive = False
        directive_base_indent = 0

        for i, line in enumerate(lines):
            stripped = line.strip()
            if stripped:
                # Normalize whitespace: replace multiple consecutive spaces with single space
                normalized = re.sub(r"\s+", " ", stripped)

                if in_code_block:
                    # Check if we should exit code block (line has less indentation)
                    original_indent = len(line) - len(line.lstrip())
                    if original_indent < code_block_base_indent:
                        # Exit code block and add blank line after it
                        in_code_block = False
                        processed_lines.append("")

                # Determine how to emit this line
                skip_normal = False

                if in_code_block:
                    # Preserve relative indentation within code blocks
                    # Example: If first code line has 16 spaces and current line has 20,
                    # relative_indent = 20-16 = 4, resulting in 6 base + 4 = 10 total spaces
                    original_indent = len(line) - len(line.lstrip())
                    relative_indent = original_indent - code_block_base_indent
                    processed_lines.append(" " * (indent + 3) + " " * relative_indent + stripped)
                    skip_normal = True
                elif in_directive:
                    original_indent = len(line) - len(line.lstrip())
                    if original_indent > directive_base_indent:
                        # Directive option or body content — preserve relative indentation
                        # so that e.g. ``:width: 50%`` stays indented under ``.. image::``.
                        relative_indent = original_indent - directive_base_indent
                        processed_lines.append(" " * indent + " " * relative_indent + stripped)
                        prev_was_list_item = False
                        skip_normal = True
                    else:
                        # Indentation dropped back — we have left the directive block.
                        in_directive = False
                        # Fall through to normal processing below.

                if not skip_normal:
                    # Check if this is a list item (bullet or numbered)
                    is_list_item = normalized.startswith("-") or re.match(
                        r"^\d+\.", normalized
                    )

                    # Add blank line when transitioning from list to non-list
                    if prev_was_list_item and not is_list_item and processed_lines:
                        processed_lines.append("")

                    # Add blank line before first list item if previous line wasn't a list item
                    if is_list_item and processed_lines and not prev_was_list_item:
                        processed_lines.append("")

                    # Add directive-body indentation
                    processed_lines.append(" " * indent + normalized)

                    # Check if line opens an RST directive (e.g. ``.. image:: path``).
                    # Directive options/content follow immediately without a blank line,
                    # so we enter directive mode and suppress the trailing blank.
                    if _RST_DIRECTIVE_RE.match(normalized):
                        in_directive = True
                        directive_base_indent = len(line) - len(line.lstrip())

                    # Check if line ends with :: (code block marker)
                    elif normalized.endswith("::"):
                        # Check if next line exists and is not empty
                        if i < len(lines) - 1 and lines[i + 1].strip():
                            # Add blank line after :: marker and enter code block mode
                            processed_lines.append("")
                            in_code_block = True
                            # Calculate base indentation from first code line to preserve
                            # relative indentation structure within the code block
                            next_line = lines[i + 1]
                            code_block_base_indent = len(next_line) - len(
                                next_line.lstrip()
                            )

                    prev_was_list_item = is_list_item
            else:
                # Preserve empty lines for paragraph separation
                processed_lines.append("")
                prev_was_list_item = False
                # Exit code block on empty line.
                # Keep directive mode so blocks like ``.. list-table::`` can contain
                # a blank separator line before their body rows.
                in_code_block = False

        return "\n".join(processed_lines)

    @staticmethod
    def _build_parent_tree(sections, root: Node) -> Node:
        """Build a parent tree from a section hierarchy.
        Args:
            sections: List of TRLC Section objects (outermost first) or None
            root: Root node to build from
        Returns:
            Leaf node of the built tree
        """
        if not sections:
            return root
        current = root

        for section in sections:
            current = Node(section.name, parent=current)
        return current

    def render(
        self,
        output_path: str,
        title: str = "Requirements",
        fields: list[str] | None = None,
        records: set[str] | None = None,
    ) -> None:
        """Parse TRLC files and render them to reStructuredText.

        Idempotent: if :meth:`parse_trlc_files` was already called (e.g. to
        warm the symbol cache before multiple render calls), parsing is skipped.

        Args:
            output_path: Path of the RST file to write.
            title: Section title.  Pass an empty string to omit it.
            fields: Field names to render.  Defaults to ``["description"]``.
            records: Optional set of fully-qualified names to include
                (additional filter on top of the source-file filter).
        """
        self.parse_trlc_files()
        self.convert_symbols_to_tree(records)
        self.render_to_file(output_path, title=title, fields=fields)


def argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    parser.add_argument("-o", "--output", required=True, help="Output RST file path")
    parser.add_argument(
        "-i",
        "--input-dir",
        default=None,
        help="Directory to scan for TRLC files. When omitted, --source-files "
        "and --dep-files are used to register files individually.",
    )
    parser.add_argument(
        "-s",
        "--source-files",
        nargs="+",
        default=None,
        help="TRLC files to render. When --input-dir is omitted these files are "
        "also registered for parsing. When --input-dir is given they act as a "
        "render filter (other record objects in the directory are not rendered).",
    )
    parser.add_argument(
        "-d",
        "--dep-files",
        nargs="+",
        default=None,
        help="Additional .rsl / .trlc files to register for dependency resolution "
        "only (not rendered). Only used when --input-dir is omitted.",
    )
    parser.add_argument(
        "-t",
        "--title",
        default="Requirements",
        help="Section title written at the top of the output file. "
        "Pass an empty string to omit the title entirely "
        "(useful when the output is included inside an already-titled section).",
    )
    parser.add_argument(
        "-f",
        "--fields",
        nargs="+",
        default=None,
        help="Field names to render for each record (e.g. ``guideword status description``). "
        "Labels are derived automatically.  Defaults to description only.",
    )
    parser.add_argument(
        "-r",
        "--records",
        nargs="+",
        default=None,
        help="Fully-qualified record names to render (e.g. ``Pkg.Record``). "
        "Acts as an additional filter on top of --source-files / --input-dir.",
    )

    return parser


def _parse_field_tokens(tokens: list[str] | None) -> list[str] | None:
    """Return the field-name token list, or ``None`` if none were given."""
    return tokens


def main() -> None:
    parser = argument_parser()
    args = parser.parse_args()

    if args.input_dir is None and not args.source_files:
        parser.error("Either --input-dir or --source-files must be provided.")

    try:
        renderer = TRLCRST(
            args.input_dir,
            source_files=args.source_files,
            dep_files=args.dep_files,
        )
        renderer.render(
            args.output,
            title=args.title,
            fields=_parse_field_tokens(args.fields),
            records=set(args.records) if args.records else None,
        )
    except TRLCParseError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
