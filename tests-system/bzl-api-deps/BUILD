load("//:trlc.bzl", "trlc_requirements", "trlc_requirements_test", "trlc_specification")

trlc_specification(
    name = "base_spec",
    srcs = ["base_schema.rsl"],
)

trlc_requirements(
    name = "base_reqs",
    srcs = ["base_items.trlc"],
    spec = [":base_spec"],
)

trlc_specification(
    name = "ext_spec",
    srcs = ["ext_schema.rsl"],
)

trlc_requirements(
    name = "ext_reqs",
    srcs = ["ext_items.trlc"],
    spec = [":ext_spec"],
    deps = [":base_reqs"],
)

trlc_requirements_test(
    name = "bzl-api-deps-test",
    reqs = [":ext_reqs"],
)
