"""Example: generate an RST document from TRLC requirements using trlc_rst.

Run with:
  bazel build //tools/trlc_rst/example:requirements_rst

The output file appears at:
  bazel-bin/tools/trlc_rst/example/requirements_rst.rst
"""

load("//:trlc.bzl", "trlc_requirements", "trlc_rst", "trlc_specification")

trlc_specification(
    name = "spec",
    srcs = ["schema.rsl"],
)

trlc_requirements(
    name = "reqs",
    srcs = ["requirements.trlc"],
    spec = [":spec"],
)

trlc_rst(
    name = "requirements_rst",
    reqs = [":reqs"],
    # title = "",  # pass an empty string to omit the top-level heading
)
