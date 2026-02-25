load("//bazel/_private:system_test.bzl", "trlc_system_test")

# ---------------------------------------------------------------------------
# System integration tests
# ---------------------------------------------------------------------------
# Test directories are discovered dynamically via glob.  Any subdirectory
# that contains an ``output`` golden file is treated as a test.  Sub-packages
# (the bzl-api-* directories) have their own BUILD files and are excluded.
_SUBPACKAGES = [
    "bzl-api-deps",
    "bzl-api-simple",
    "bzl-api-spec-check",
]

_ALL_TESTS = [
    f.split("/")[0]
    for f in glob(["*/output"])
    if f.split("/")[0] not in _SUBPACKAGES
]

[trlc_system_test(test_dir = d) for d in _ALL_TESTS]

# "slow" tests are excluded from the :fast suite but included in :all_tests.
# Currently only "bulk" qualifies; add further names here if needed.
_SLOW_TESTS = ["bulk"]

test_suite(
    name = "fast",
    tests = [":" + d for d in _ALL_TESTS if d not in _SLOW_TESTS],
)

test_suite(
    name = "all_tests",
    tests = [":" + d for d in _ALL_TESTS],
)

# ---------------------------------------------------------------------------
# Bazel API (trlc.bzl) integration tests
# Rules live in their own sub-packages; this suite aggregates them.
# ---------------------------------------------------------------------------

test_suite(
    name = "bzl_api",
    tests = [
        "//tests-system/bzl-api-simple:bzl-api-simple-test",
        "//tests-system/bzl-api-deps:bzl-api-deps-test",
        "//tests-system/bzl-api-spec-check:bzl-api-spec-check-test",
    ],
)
