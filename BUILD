load("@rules_python//python:defs.bzl", "py_binary", "py_test")
load("@rules_python//python:pip.bzl", "compile_pip_requirements")
load("@rules_shell//shell:sh_binary.bzl", "sh_binary")
load("@rules_shell//shell:sh_test.bzl", "sh_test")
load("@trlc_dev_dependencies//:requirements.bzl", "requirement")

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

# Run: bazel run //:requirements_3_XX.update  --@@rules_python+//python/config_settings:python_version=3.XX
[
    compile_pip_requirements(
        name = "requirements_3_{}".format(version),
        src = "requirements.txt",
        python_version = "3.{}".format(version),
        requirements_txt = "requirements_lock_3_{}.txt".format(version),
    )
    for version in [
        "9",
        "10",
        "11",
        "12",
    ]
]

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
    name = "coverage_cfg",
    srcs = ["coverage.cfg"],
    visibility = ["//visibility:public"],
)

# LINTING & CODE QUALITY

py_test(
    name = "style",
    srcs = glob([
        "trlc*.py",
        "lobster-*.py",
    ]) + [
        "//trlc:py_sources",
        "//util:pycodestyle_runner.py",
    ],
    data = ["setup.cfg"],
    main = "pycodestyle_runner.py",
    deps = [requirement("pycodestyle")],
)

sh_test(
    name = "lint-pylint",
    srcs = ["//util:lint_check.sh"],
    data = [
        "pylint3.cfg",
        "//trlc:py_sources",
    ] + glob([
        "trlc*.py",
        "lobster-*.py",
    ]),
)

test_suite(
    name = "lint",
    tests = [
        ":lint-pylint",
        ":style",
    ],
)

sh_binary(
    name = "clean-coverage",
    srcs = ["//util:clean_coverage.sh"],
    tags = ["manual"],
    visibility = ["//visibility:public"],
)
