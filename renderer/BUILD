load("@rules_python//python:pip.bzl", "compile_pip_requirements")
load("@trlc_renderer_dependencies//:requirements.bzl", "requirement")


compile_pip_requirements(
    name = "requirements",
    src = "requirements.in",
    requirements_txt = "requirements_lock.txt",
)

py_binary(
    name = "trlc_renderer",
    srcs = ["trlc_renderer.py"],
    visibility = ["//visibility:public"],
    deps = [
        requirement("bigtree"),
        requirement("pydot"),
        "//trlc",
    ],
)
