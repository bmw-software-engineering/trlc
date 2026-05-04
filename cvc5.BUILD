filegroup(
    name = "cvc5",
    srcs = select({
        "@bazel_tools//src/conditions:windows": ["bin/cvc5.exe"],
        "//conditions:default": ["bin/cvc5"],
    }),
    visibility = ["//visibility:public"],
)
