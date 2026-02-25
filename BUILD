load("@rules_python//python:pip.bzl", "compile_pip_requirements")

# trlc.py is exposed for the test rule in trlc.bzl;
# pyproject.toml is needed by pylint/ty via rules_lint.
exports_files(
    [
        "trlc.py",
        "pyproject.toml",
    ],
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

# Run: bazel run //:requirements.update
compile_pip_requirements(
    name = "requirements",
    src = "requirements.txt",
    requirements_txt = "requirements.txt.bazel",
)

# Run: bazel run //:requirements_dev.update
compile_pip_requirements(
    name = "requirements_dev",
    src = "requirements_dev.txt",
    requirements_txt = "requirements_dev_lock.txt",
)

alias(
    name = "format.check",
    actual = "//tools/format:format.check",
)

alias(
    name = "format.fix",
    actual = "//tools/format:format",
)
