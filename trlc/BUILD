load("@trlc_dependencies//:requirements.bzl", "requirement")

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
    deps = [requirement("pyvcg")],
)
