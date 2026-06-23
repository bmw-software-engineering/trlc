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
    main = "trlc.py",
    visibility = ["//visibility:public"],
    deps = [
        "//trlc",
    ],
)

# Run: bazel run //:requirements.update
compile_pip_requirements(
    name = "requirements",
    src = "requirements.txt",
    requirements_txt = "requirements_lock.txt",
)

# Run: bazel run //:requirements_dev.update
compile_pip_requirements(
    name = "requirements_dev",
    src = "requirements_dev.txt",
    requirements_txt = "requirements_dev_lock.txt",
)

alias(
    name = "format.check",
    actual = "//third_party/format:format.check",
)

alias(
    name = "format.fix",
    actual = "//third_party/format:format",
)

filegroup(
    name = "coverage",
    srcs = ["coverage.cfg"],
    visibility = ["//visibility:public"],
)
