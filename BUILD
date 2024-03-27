load("@rules_python//python:pip.bzl", "compile_pip_requirements")

# This is additionally exposed for the test rule in trlc.bzl
exports_files(
    ["trlc.py"],
    visibility = ["//visibility:public"],
)

py_binary(
    name = "trlc_binary",
    srcs = [
        "trlc.py",
    ],
    args = ["--use-cvc5-binary $(location //:cvc5)"],
    data = ["//:cvc5"],
    main = "trlc.py",
    visibility = ["//visibility:public"],
    deps = [
        "//trlc",
    ],
)

alias(
    name = "cvc5",
    actual = select({
        "@bazel_tools//src/conditions:windows": "@cvc5_windows//:cvc5",
        "@bazel_tools//src/conditions:darwin": "@cvc5_mac//:cvc5",
        "//conditions:default": "@cvc5_linux//:cvc5",
    }),
    visibility = ["//visibility:public"],
)

# Run bazel run //:requirements.update
compile_pip_requirements(
    name = "requirements",
    src = "requirements.txt",
    requirements_txt = "requirements.txt.bazel",
)
