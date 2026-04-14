load("@trlc_dependencies//:requirements.bzl", "requirement")

py_library(
    name = "trlc_rst_lib",
    srcs = ["trlc_rst.py"],
    imports = ["."],
    visibility = ["//tools/trlc_rst/tests:__pkg__"],
    deps = [
        "//trlc",
        requirement("bigtree"),
    ],
)

py_binary(
    name = "trlc_rst",
    srcs = ["trlc_rst.py"],
    visibility = ["//visibility:public"],
    deps = [
        "//trlc",
        requirement("bigtree"),
    ],
)
