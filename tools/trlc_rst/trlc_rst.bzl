def trlc_rst_integration_test(test_dir):
    """Create a py_test and test_suite alias for a tools/trlc_rst/tests/ subdirectory.

    Each test directory must contain TRLC input files (*.rsl, *.trlc) and a
    golden output file named ``output.rst`` against which the rendered result
    is diffed.

    Args:
      test_dir: subdirectory name inside tools/trlc_rst/tests/.
    """
    srcs = native.glob([test_dir + "/**"])
    test_target = test_dir + "_test"

    native.py_test(
        name = test_target,
        srcs = [":converter_test.py"],
        main = "converter_test.py",
        args = [
            "tools/trlc_rst/tests",
            test_dir,
        ],
        deps = ["//tools/trlc_rst:trlc_rst_lib"],
        data = list(srcs),
    )

    native.test_suite(
        name = test_dir,
        tests = [":" + test_target],
    )
