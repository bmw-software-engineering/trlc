"""Golden-file system test runner for trlc.

Runs trlc against each output* golden file in a test directory and diffs
the results.  Extra flags may be provided via an optional ``options`` file.
"""

def trlc_system_test(test_dir):
    """Create a py_test and test_suite alias for a tests-system/ subdirectory.

    Args:
      test_dir: subdirectory name inside tests-system/.
    """
    srcs = native.glob([test_dir + "/**"])

    # cvc5 binary is always included for tests with an output.smtlib golden file.
    # The "_test" suffix avoids a runfiles symlink collision with the source dir;
    # a test_suite alias under the plain name allows: bazel test //tests-system:<dir>
    test_target = test_dir + "_test"

    native.py_test(
        name = test_target,
        srcs = ["//bazel/_private:mode_test.py"],
        main = "mode_test.py",
        args = [
            "tests-system",
            test_dir,
            "$(rlocationpath //:cvc5)",
        ],
        deps = ["//trlc:trlc"],
        data = list(srcs) + ["//:cvc5", "//:coverage"],
    )

    native.test_suite(
        name = test_dir,
        tests = [":" + test_target],
    )
