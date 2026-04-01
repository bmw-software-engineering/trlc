load("//tools/trlc_rst:trlc_rst.bzl", "trlc_rst_integration_test")

# Discover every subdirectory that contains an output.rst golden file.
_ALL_TESTS = [
    f.split("/")[0]
    for f in glob(["*/output.rst"])
]

[trlc_rst_integration_test(test_dir = d) for d in _ALL_TESTS]

test_suite(
    name = "all",
    tests = [":" + d for d in _ALL_TESTS],
)
