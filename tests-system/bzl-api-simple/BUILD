load("//:trlc.bzl", "trlc_requirements", "trlc_requirements_test", "trlc_specification")

trlc_specification(
    name = "spec",
    srcs = ["schema.rsl"],
)

trlc_requirements(
    name = "reqs",
    srcs = ["reqs.trlc"],
    spec = [":spec"],
)

trlc_requirements_test(
    name = "bzl-api-simple-test",
    reqs = [":reqs"],
)
