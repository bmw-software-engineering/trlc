load("@aspect_rules_js//js:defs.bzl", "js_library", "js_test")
load("@aspect_rules_lint//format:defs.bzl", "format_multirun")
load("@npm_trlc//:defs.bzl", "npm_link_all_packages")
load("@npm_trlc//tools/formatter:prettier/package_json.bzl", prettier = "bin")
load("@rules_multirun//:defs.bzl", "command")

package(default_visibility = ["//visibility:public"])

exports_files([
    ".npmrc",
    "package.json",
    "pnpm-lock.yaml",
])

npm_link_all_packages(name = "node_modules")

js_library(
    name = "prettier_plugin_lib",
    srcs = [
        "src/index.js",
        "src/language.js",
        "src/options.js",
        "src/parser.js",
        "src/printer.js",
        "src/trlc-lexer.js",
        "src/trlc-node.js",
        "src/trlc-parser-impl.js",
    ],
)

js_library(
    name = "prettierrc",
    srcs = ["prettier.config.mjs"],
    deps = [":prettier_plugin_lib"],
)

js_test(
    name = "unit_test",
    data = [
        "src/printer.unit.test.js",
        ":node_modules/prettier",
        ":prettier_plugin_lib",
    ],
    entry_point = "src/printer.unit.test.js",
    node_options = ["--test"],
)

prettier.prettier_binary(
    name = "prettier_trlc_formatter",
    data = [":prettierrc"],
    env = {
        "BAZEL_BINDIR": ".",
    },
    fixed_args = [
        "--config=\"$$JS_BINARY__RUNFILES\"/$(rlocationpath :prettierrc)",
        "--log-level=warn",
    ],
    visibility = ["//visibility:public"],
)

format_multirun(
    name = "format",
    trlc = ":prettier_trlc_formatter",
    visibility = ["//visibility:public"],
)

command(
    name = "cmd-format-trlc",
    command = ":format",
    run_from_workspace_root = True,
)

command(
    name = "cmd-format-trlc-check",
    command = ":format.check",
    run_from_workspace_root = True,
)
