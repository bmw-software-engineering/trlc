load("//:trlc.bzl", "trlc_requirements", "trlc_requirements_test", "trlc_specification", "trlc_specification_test")

# Run all passing tests in this package: bazel test //api-examples/filename-check
test_suite(
    name = "filename-check",
    tests = [
        ":spec_check",
        ":validate",
    ],
)


# 1. Gather the RSL schema
trlc_specification(
    name = "spec",
    srcs = ["example.rsl"],
    visibility = ["//api-examples:__subpackages__"],
)

# 2. Gather the requirements
trlc_requirements(
    name = "reqs",
    srcs = ["example.trlc"],
    spec = [":spec"],
)

# 3. Validate that the RSL schema itself is consistent
trlc_specification_test(
    name = "spec_check",
    reqs = [":reqs"],
)

# 4. Standard built-in validation (trlc --verify)
trlc_requirements_test(
    name = "validate",
    reqs = [
        ":reqs",
    ],
)

# 5. Custom validation script: checks that illustration filenames exist on disk
trlc_requirements_test(
    name = "filename_check",
    srcs = [":filename-3.py"],
    main = "filename-3.py",
    reqs = [
        ":reqs",
    ],
)
