load("//:trlc.bzl", "trlc_requirements", "trlc_specification", "trlc_specification_test")

trlc_specification(
    name = "spec",
    srcs = ["types.rsl"],
)

trlc_requirements(
    name = "reqs",
    srcs = ["placeholder.trlc"],
    spec = [":spec"],
)

trlc_specification_test(
    name = "bzl-api-spec-check-test",
    reqs = [":reqs"],
)
