import argparse
import re
import logging
import json  # Import json for loading the mapping file
from bigtree import Node, preorder_iter
import trlc.ast
from trlc.errors import Message_Handler
from trlc.trlc import Source_Manager

RST_HEADLINE_SEPERATOR = {
    0: "**********",
    1: "==========",
    2: "----------",
    3: "^^^^^^^^^^",
}

class TRLCRenderer:
    def __init__(self, input_directory: str, output_path: str, mapping_file: str = None, debug: bool = False):
        self.input_directory = input_directory
        self.output_path = output_path
        self.debug = debug
        self.symbols = None
        self.requirements = None
        self.req_objects = None
        self.type_mapping = self.load_type_mapping(mapping_file)  # Load the mapping file if provided

        if self.debug:
            logging.basicConfig(level=logging.DEBUG)

    def load_type_mapping(self, mapping_file: str) -> dict:
        """Load the requirement type mapping from a JSON file or return an empty mapping."""
        if mapping_file:
            with open(mapping_file, 'r') as file:
                mapping = json.load(file)
            logging.debug("Loaded type mapping successfully.")
            return mapping
        else:
            logging.debug("No mapping file provided; using default types.")
            return {}  # Return an empty mapping if no file is provided

    def parse_trlc_files_in(self) -> trlc.ast.Symbol_Table:
        message_handler = Message_Handler()
        source_manager = Source_Manager(message_handler)
        source_manager.register_directory(self.input_directory)
        self.symbols = source_manager.process()

        if self.symbols is None:
            raise ValueError("Failed to parse TRLC Files")

        logging.debug("Parsed TRLC files successfully.")
        return self.symbols

    def convert_symbols_to_objects(self):
        requirements_root = Node("root")
        object_list = {}

        for obj in self.symbols.iter_record_objects():
            parent_tree = self.build_parent_tree(obj.section, Node("root"))
            parent_tree.append(Node(obj.fully_qualified_name()))
            object_list[obj.fully_qualified_name()] = obj

            # Merge both trees
            to_tree = requirements_root
            for from_node in preorder_iter(parent_tree):
                if from_node.is_root:
                    continue

                found_node = next((to_node for to_node in to_tree.children if to_node.name == from_node.name), None)
                if found_node is None:
                    to_tree.append(from_node)
                    break
                else:
                    to_tree = found_node

        self.requirements = requirements_root
        self.req_objects = object_list
        logging.debug("Converted symbols to objects successfully.")

    def apply_case_format(self, value: str, case_format: str) -> str:
        """Apply the specified case format to a string."""
        if case_format == "snake_case":
            return re.sub(r'(?<!^)(?=[A-Z])', '_', value).lower()
        elif case_format == "camelCase":
            return value[0].lower() + value[1:]
        elif case_format == "screaming_snake_case":
            return value.upper()
        return value  # Default case (no change)

    def generate_need_id(self, reqobj) -> str:
        """Generates a unique identifier for a requirement object based on its type, package,
           and its name using the format specified in the mapping file."""
        req_type = reqobj.n_typ.name
        req_package = reqobj.n_package.name
        req_name = reqobj.name

        # Get the ID format from the mapping
        mapped_type, _, _ = self.map_requirement_type(req_type)

        id_format = self.type_mapping.get(req_type, {}).get("generate_id_format")

        # If no format is defined, use only the name
        if id_format is None:
            return req_name  # Return only the name if no format is defined

        # Get the casing formats
        id_case_format = self.type_mapping.get(req_type, {}).get("id_case_format", {})
        formatted_type = self.apply_case_format(mapped_type, id_case_format.get("type", ""))
        formatted_package = self.apply_case_format(req_package, id_case_format.get("package", ""))
        formatted_name = self.apply_case_format(req_name, id_case_format.get("name", ""))

        # Format the ID using the specified format
        return id_format.format(type=formatted_type, package=formatted_package, name=formatted_name)

    def generate_link_id_score(self, link, objects) -> str:
        """Generates a unique identifier for a link object based on its identifier and version,
           using the same format as defined in generate_id_format."""
        linkobj = objects[link['item']]
        # Use the same ID format for links
        return self.generate_need_id(linkobj) + f"@{link['LinkVersion']}"

    def get_link_attribute_value(self, value) -> str:
        """Generates the attribute value for link attributes."""
        return ', '.join(self.generate_link_id_score(v, self.req_objects) for v in value if v is not None)

    def map_requirement_type(self, req_type: str) -> tuple:
        """Maps the requirement type using the loaded mapping or returns the original type and attributes."""
        mapping = self.type_mapping.get(req_type)
        if mapping is None:
            logging.debug(f"Type {req_type} not found in mapping, using {req_type} with default attributes.")
            return req_type, [], []  # Return original type and empty attributes if not found

        # Extract the mapped type, attributes, and links
        mapped_type = mapping.get("mapped_type", req_type)
        attributes = mapping.get("attributes", [])
        links = mapping.get("links", [])

        return mapped_type, attributes, links  # Return mapped type, attributes, and links
    def _convert_to_title(self, identifier: str) -> str:
        transformed_title=""
        for i in identifier:
            if i.isupper():
                transformed_title+=" "+i
            else:
                transformed_title+=i
        return transformed_title.join(" ")

    def render_restructured_text_file(self):
        with open(self.output_path, "w", newline="") as file:
            file.write("Requirements\n============\n")

            for node in preorder_iter(self.requirements):
                if node.is_root:
                    continue

                if node.is_leaf:
                    reqobj = self.req_objects[node.name]
                    req_type = reqobj.n_typ.name  # Get the requirement type
                    mapped_type, attributes_to_export, links_to_export = self.map_requirement_type(req_type)  # Use mapping

                    title = self._convert_to_title(node.name)
                    id = self.generate_need_id(reqobj)

                    # Write the requirement header
                    file.write(f".. {mapped_type}:: {title}\n")
                    file.write(f"   :id: {id}\n")

                    reqobjpython_dict = reqobj.to_python_dict()
                    for attr in attributes_to_export:
                        # Split the attribute and default value if specified
                        if '=' in attr:
                            key, default_value = map(str.strip, attr.split('=', 1))
                        else:
                            key, default_value = attr, "Not specified"

                        if key not in reqobjpython_dict:
                            # Use default value if the attribute is not defined
                            file.write(f"   :{key}: {default_value}\n")
                            continue

                        value = reqobjpython_dict[key]
                        if key in links_to_export:
                            attr_val = self.get_link_attribute_value(value)
                            file.write(f"   :{key}: {attr_val}\n")
                        else:
                            # Handle regular attributes
                            if isinstance(value, list):
                                attr_val = ', '.join(
                                    str(v) if not isinstance(v, dict) else ', '.join(f"{v2}" for v2 in v.values())
                                    for v in value if v is not None
                                )
                            else:
                                attr_val = str(value) if not isinstance(value, dict) else ', '.join(f"{v2}" for v2 in value.values())

                            file.write(f"   :{key}: {attr_val}\n")

                    # Output links even if they are not in attributes
                    for link in links_to_export:
                        if link in reqobjpython_dict:
                            link_value = reqobjpython_dict[link]
                            link_attr_val = self.get_link_attribute_value(link_value)
                            file.write(f"   :{link}: {link_attr_val}\n")

                    # Write the description at the end
                    file.write(f"   {reqobj.field['description'].value}\n\n\n")

    def build_parent_tree(self, section: trlc.ast.Section, root) -> Node:
        if section is None:
            return root
        parent = self.build_parent_tree(section.parent, root)
        return Node(section.name, parent=parent)

    def run(self):
        self.parse_trlc_files_in()
        self.convert_symbols_to_objects()
        self.render_restructured_text_file()


def argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    parser.add_argument("-o", "--output", required=True, help="Output file path")
    parser.add_argument("-m", "--mapping", help="Path to the JSON mapping file (optional)")
    parser.add_argument("--debug", action='store_true', help="Enable debug output")
    return parser


def main() -> None:
    parser = argument_parser()
    args = parser.parse_args()

    renderer = TRLCRenderer(".", args.output, args.mapping, args.debug)
    renderer.run()


if __name__ == "__main__":
    main()
