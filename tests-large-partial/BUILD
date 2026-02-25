load("@rules_python//python:defs.bzl", "py_binary")
load("//bazel/_private:partial_test.bzl", "trlc_partial_test")

# ---------------------------------------------------------------------------
# Large partial-loading tests
# ---------------------------------------------------------------------------
# Tests are discovered dynamically: any subdirectory containing an ``output``
# golden file is a test.  The ``large/`` corpus directory has no ``output``
# file and is therefore not picked up.
_TESTS = [
    f.split("/")[0]
    for f in glob(["*/output"])
]

[trlc_partial_test(test_name = t) for t in _TESTS]

test_suite(
    name = "partial_tests",
    tests = [":" + t for t in _TESTS],
)
