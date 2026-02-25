"""Bazel macro for tests-large-partial/ golden-file tests.

``trlc_partial_test(test_name)`` creates one ``native.py_test`` that reuses
the shared ``mode_test.py`` runner from ``//bazel/_private``.

The test subdirectory must contain:

* ``output``  -- golden output (only this one mode is checked)
* ``options`` -- extra trlc flags, e.g. ``--show-file-list -I large large/pkg.trlc``
                 (paths are relative to ``tests-large-partial/``)

Args forwarded via Bazel ``args`` to ``mode_test.py``:

.. code-block:: text

    argv[1]  root_dir   "tests-large-partial"
    argv[2]  test_dir   plain string, e.g. "partial-1"
    argv[3]  cvc5_rloc  $(rlocationpath //:cvc5)
"""

def trlc_partial_test(test_name):
    """Create a golden-file py_test for a tests-large-partial/ subdirectory.

    Args:
      test_name: subdirectory name, e.g. ``"partial-1"``.
    """
    srcs = native.glob([test_name + "/**"])

    # NOTE: the py_test must NOT be named test_name because Bazel would create
    # a runfiles symlink  tests-large-partial/<test_name> -> bazel-out/…/<name>
    # that obscures the source-directory symlinks for the golden files inside
    # it.  The "_test" suffix avoids that collision.  A test_suite under the
    # plain name preserves the short invocation style.
    test_target = test_name + "_test"

    native.py_test(
        name = test_target,
        srcs = ["//bazel/_private:mode_test.py"],
        main = "mode_test.py",
        args = [
            "tests-large-partial",
            test_name,
            "$(rlocationpath //:cvc5)",
        ],
        deps = ["//trlc:trlc"],
        data = list(srcs) + native.glob(["large/**"]) + ["//:cvc5", "//:coverage"],
        size = "large",
    )

    native.test_suite(
        name = test_name,
        tests = [":" + test_target],
    )
