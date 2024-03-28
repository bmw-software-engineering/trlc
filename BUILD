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
    args = ["--use-cvc5-binary $(location @cvc5)"],
    data = ["@cvc5"],
    main = "trlc.py",
    visibility = ["//visibility:public"],
    deps = [
        "//trlc",
    ],
)

alias(
    name = "cvc5",
    actual = "@cvc5",
    visibility = ["//visibility:public"],
)
