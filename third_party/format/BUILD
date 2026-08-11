load("@aspect_rules_lint//format:defs.bzl", "format_multirun")

exports_files([
    "add_trlc_support.patch",
])

format_multirun(
    name = "format",
    python = "@aspect_rules_lint//format:ruff",
    starlark = "@buildifier_prebuilt//:buildifier",
    trlc = "//tools/formatter:prettier_trlc_formatter",
    visibility = ["//visibility:public"],
)


