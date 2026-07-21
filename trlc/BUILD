load("@rules_python//python:defs.bzl", "py_library")
load("@trlc_dependencies//:requirements.bzl", "requirement")

filegroup(
    name = "py_sources",
    srcs = glob(["*.py"]),
    visibility = ["//visibility:public"],
)

py_library(
    name = "trlc",
    srcs = [
        "__init__.py",
        "__main__.py",
        "ast.py",
        "errors.py",
        "lexer.py",
        "lint.py",
        "math.py",
        "nested.py",
        "parser.py",
        "trlc.py",
        "vcg.py",
        "version.py",
    ],
    visibility = ["//visibility:public"],
    deps = [
        requirement("pyvcg"),
        requirement("cvc5"),
    ],
)
