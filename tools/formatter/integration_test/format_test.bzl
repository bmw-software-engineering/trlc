"""Integration test macro for the TRLC Prettier formatter.

Each subdirectory containing input.trlc + expected.trlc (or input.rsl + expected.rsl)
becomes one test case:
  - js_run_binary runs prettier on the input file and captures stdout
  - diff_test compares the actual output to the expected file

## Adding a new test case

1. Create a new subdirectory under integration_test/ (e.g. my_feature/).
2. Add input.<ext> (the unformatted source) and expected.<ext> (desired output).
3. No changes to BUILD files are required — the glob picks up new directories.

## Testing non-default formatter options

If the test case needs to override Prettier or trlc* options, place an
options.json file in the case directory alongside input/expected:

    integration_test/my_feature/options.json:
    {
        "useTabs": true,
        "trlcSortImports": false,
        "trlcAttributeGap": 0
    }

The macro automatically detects the options.json file, adds it to the Bazel
sandbox as a data dependency, and passes its path as a second argument to
format_via_api.mjs, which merges the options into the Prettier call.

Supported keys: any valid Prettier option or trlc* custom option.
"""

load("@aspect_rules_js//js:defs.bzl", "js_run_binary")
load("@bazel_skylib//rules:diff_test.bzl", "diff_test")

def trlc_format_test_suite(name, prettier):
    """Create one diff_test per input/expected pair found in subdirectories.

    Args:
        name: name of the resulting test_suite target
        prettier: label of the prettier js_binary to use for formatting
    """
    tests = []

    for ext in ["trlc", "rsl"]:
        cases = [
            f[:-len("/input." + ext)]
            for f in native.glob(["*/input." + ext])
        ]

        for case in cases:
            test_name = case + "_" + ext

            # Detect an optional options.json in the test case directory.
            # If present, it is added as a data dependency and passed as a
            # second argument to format_via_api.mjs so non-default Prettier
            # or trlc* options can be exercised per test case.
            options_files = native.glob([case + "/options.json"], allow_empty = True)
            has_options = len(options_files) > 0

            srcs = [case + "/input." + ext]
            args = ["$(rootpath " + case + "/input." + ext + ")"]
            if has_options:
                srcs = srcs + [case + "/options.json"]
                args = args + ["$(rootpath " + case + "/options.json)"]

            js_run_binary(
                name = test_name + "_actual",
                srcs = srcs,
                stdout = test_name + "_actual." + ext,
                args = args,
                tool = prettier,
                testonly = True,
            )

            diff_test(
                name = test_name + "_test",
                file1 = test_name + "_actual",
                file2 = case + "/expected." + ext,
            )

            tests.append(test_name + "_test")

    native.test_suite(
        name = name,
        tests = tests,
    )
