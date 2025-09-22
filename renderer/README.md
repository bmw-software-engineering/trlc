# Renderer

`Renderer` helps to view requirements written in TRLC as ReStructuredText.
This way, it is possible to generate and HTML or PDF version of them, using Sphinx.

The `Renderer` can be used as follows

```
load("//tools/trlc_renderer:trlc_renderer.bzl", "trlc_renderer")
load("@trlc//:trlc.bzl", "trlc_requirements")

trlc_requirements(
    name = "some_requriement",
    srcs = ["some_requirement.trlc"],
    spec = [...],
)

trlc_renderer(
    name = "requirements",
    reqs = [":some_requirement"],
)

```

## Design

In general the `Renderer` is right now quite simple. It parses the TRLC files, using the TRLC Python library, then creates a tree of requirements including its sections. In a last step it writes the requirements in the rst file including the sections as headlines.

### Mapping

If the requirement types in the TRLC Model and in the rst file should differ it is possible to specify a mapping file (--mapping) in following format:

```json

"Type in TRLC": {
        "mapped_type": "Type in RST",
        // Specify the attributes which should be exported into the rst file. It is possible to provide a default value (attribute = value). This value applies if the attribute is not found in the TRLC model
        "attributes": [
            "status",
            "security = yes"
        ],
        // Specify the links which should be exported. In contrary to the attributes the links are formatted according to the defined format before they are written into the rst file
        "links": ["derived_from", "satisfied_by"],
        // Definition of the Format how the ID should be converted in the rst file. It is also possible to specify casing
        "generate_id_format": "{type}__{package}__{name}",
        "id_case_format": {
            "type": "screaming_snake_case",
            "package": "snake_case",
            "name": "snake_case"
        }
    },

```

If no mapping file is specified all types and attributes are exported 1:1 into the rst file.

### Sequence Diagram

[TRLC Renderer Sequence Diagramm](assets/trlc_renderer_seq.puml)
