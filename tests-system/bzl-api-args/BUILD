load("//:trlc.bzl", "trlc_requirements", "trlc_requirements_test", "trlc_specification", "trlc_specification_test")

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
    name = "bzl-api-args-test",
    args = ["--skip-trlc-files"],
    reqs = [":reqs"],
)

trlc_specification_test(
    name = "bzl-api-args-spec-test",
    args = ["--no-lint"],
    reqs = [":spec"],
)
