"""File system test runner for the trlc repository.

``trlc_system_test(test_dir)`` creates one ``native.py_test`` per test
directory.  Inside ``mode_test.py`` each available output mode is run
sequentially; failures are collected and reported at the end.

Each mode invokes ``trlc --log`` (writes output to a file) and
diffs the result against the committed golden file.

Which modes are run is determined at runtime by ``mode_test.py`` by listing
the ``output*`` golden files present in the test directory.  Extra trlc flags
(e.g. ``--no-detailed-info``) are read from an optional ``options`` file
inside the test directory.
"""

def trlc_system_test(test_dir):
    """Create a single golden-file py_test for a tests-system/ directory.

    Args forwarded via Bazel ``args`` to ``mode_test.py``:

    .. code-block:: text

        argv[1]  root_dir   "tests-system"
        argv[2]  test_dir   plain string, e.g. "checks-1"
        argv[3]  cvc5_rloc  $(rlocationpath //:cvc5)

    Available modes are discovered at runtime from the ``output*`` files
    present in the test directory.  An optional ``options`` file in the
    directory may contain extra trlc flags (one per line or whitespace-
    separated), e.g. ``--no-detailed-info``.

    Two Bazel targets are created (example for ``test_dir = "checks-1"``):

    .. code-block:: text

        //tests-system:checks-1_test  (py_test)
        //tests-system:checks-1       (test_suite alias)

    Args:
      test_dir: subdirectory name inside tests-system/.
    """
    srcs = native.glob([test_dir + "/**"])

    # cvc5 is always needed: "output" mode (always present) requires it.
    #
    # NOTE: the py_test must NOT be named test_dir because Bazel would create
    # a runfiles symlink  tests-system/<test_dir> -> bazel-out/…/<test_dir>
    # that obscures the source-directory symlinks for the golden files inside
    # it.  The "_test" suffix avoids that collision.  A test_suite under the
    # plain test_dir name preserves the short  bazel test //tests-system:<dir>
    # invocation.
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
