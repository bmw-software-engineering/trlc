load("//:trlc.bzl", "trlc_requirements", "trlc_requirements_test", "trlc_specification")

trlc_specification(
    name = "spec",
    srcs = ["example.rsl"],
    visibility = ["//api-examples:__subpackages__"],
)

trlc_requirements(
    name = "reqs",
    srcs = ["example.trlc"],
    spec = [":spec"],
)

trlc_requirements_test(
    name = "foo",
    reqs = [
        ":reqs",
    ],
)

trlc_requirements_test(
    name = "bar",
    srcs = [":filename-3.py"],
    main = "filename-3.py",
    reqs = [
        ":reqs",
    ],
)
