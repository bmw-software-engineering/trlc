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
        """
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

    def convert_symbols_to_tree(self) -> None:
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
        """
        if self._symbols is None:
            raise ValueError("Symbols not parsed. Call parse_trlc_files() first.")

        source_file_set = self._resolve_source_files()

        requirements_root = Node("root")
        obj: trlc.ast.Record_Object
        for obj in self._symbols.iter_record_objects():
            # If source files are specified, only include objects from those files
            if source_file_set is not None:
                obj_file = os.path.abspath(obj.location.file_name)
                if obj_file not in source_file_set:
                    continue
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

    def render_to_file(self, output_path: str, title: str = "Requirements") -> None:
        """Render the requirements tree to a reStructuredText file.

        Args:
            output_path: Path of the RST file to write.
            title: Section title written at the top of the file.
                   Pass an empty string to omit the title entirely
                   (useful when the output is ``.. include::``d inside an
                   already-titled section).
        """

        if self._requirements_tree is None:
            raise ValueError(
                "Requirements tree not built. Call convert_symbols_to_tree() first."
            )

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
                    file.write(f".. requirement:definition:: {node.name}\n\n")
                    trlc_obj = getattr(node, "trlc_obj", None)

                    if trlc_obj:
                        description = trlc_obj.to_python_dict().get("description")
                        if description:
                            file.write(self._preprocess_description(description))
                    file.write("\n\n")

    @staticmethod
    def _preprocess_description(description: str) -> str:
        """Preprocess a description for proper reStructuredText formatting.

        Supported RST formatting in descriptions:
        - **Bold text**: **text**
        - *Italic text*: *text*
        - Inline code: ``code``
        - Hyperlinks: [text](url) converted to `text <url>`_
        - Code blocks: Line ending with :: followed by indented content
        - Bullet lists: Lines starting with -
        - Numbered lists: Lines starting with 1., 2., etc.
        - Line breaks: Preserved between all content lines"""
        if not description:
            return description

        # Convert Markdown-style links [text](url) to RST-style `text <url>`_
        description = re.sub(r"\[([^\]]+)\]\(([^\)]+)\)", r"`\1 <\2>`_", description)

        lines = description.split("\n")
        processed_lines = []
        prev_was_list_item = False
        in_code_block = False
        code_block_base_indent = 0

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

                if in_code_block:
                    # Preserve relative indentation within code blocks
                    # Example: If first code line has 16 spaces and current line has 20,
                    # relative_indent = 20-16 = 4, resulting in 6 base + 4 = 10 total spaces
                    original_indent = len(line) - len(line.lstrip())
                    relative_indent = original_indent - code_block_base_indent
                    processed_lines.append("      " + " " * relative_indent + stripped)
                else:
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

                    # Add RST directive content indentation (3 spaces)
                    processed_lines.append("   " + normalized)

                    # Check if line ends with :: (code block marker)
                    if normalized.endswith("::"):
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

                    # Add blank line after non-list lines to preserve line breaks
                    # (unless next line is empty, we're at the end, or we're in a code block)
                    elif (
                        not is_list_item
                        and not in_code_block
                        and i < len(lines) - 1
                        and lines[i + 1].strip()
                    ):
                        processed_lines.append("")

                    prev_was_list_item = is_list_item
            else:
                # Preserve empty lines for paragraph separation
                processed_lines.append("")
                prev_was_list_item = False
                # Exit code block on empty line
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

    def render(self, output_path: str, title: str = "Requirements") -> None:
        """Parse TRLC files and render them to reStructuredText.

        Args:
            output_path: Path of the RST file to write.
            title: Section title. Pass an empty string to omit it.
        """
        self.parse_trlc_files()
        self.convert_symbols_to_tree()
        self.render_to_file(output_path, title=title)


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

    return parser


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
        renderer.render(args.output, title=args.title)
    except TRLCParseError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
