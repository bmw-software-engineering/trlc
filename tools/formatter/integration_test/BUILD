"""Integration tests for the TRLC Prettier formatter."""

load("@aspect_rules_js//js:defs.bzl", "js_binary")
load(":format_test.bzl", "trlc_format_test_suite")

js_binary(
    name = "format_via_api",
    testonly = True,
    data = [
        "//tools/formatter:node_modules/prettier",
        "//tools/formatter:prettier_plugin_lib",
    ],
    entry_point = "format_via_api.mjs",
)

trlc_format_test_suite(
    name = "all",
    prettier = ":format_via_api",
)
