load("@rules_python//python:defs.bzl", "py_binary")
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
    name = "coverage",
    srcs = ["coverage.cfg"],
    visibility = ["//visibility:public"],
)

# ---------------------------------------------------------------------------
# Top-level test suites aggregating all three test packages.
# bazel test //:fast       -- unit + system fast + partial tests
# bazel test //:all_tests  -- unit + system all  + partial tests
# ---------------------------------------------------------------------------
test_suite(
    name = "fast",
    tests = [
        "//tests-large-partial:fast",
        "//tests-system:fast",
        "//tests-unit:unit_tests",
    ],
)

test_suite(
    name = "all_tests",
    tests = [
        "//tests-large-partial:all",
        "//tests-system:all_tests",
        "//tests-unit:unit_tests",
    ],
)
