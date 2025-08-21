TrlcProviderInfo = provider(
    fields = {
        "spec": "Holds the specification files (*.rsl) for the `reqs`",
        "reqs": "Holds the requirement files (*.trlc)",
    },
)

def _trlc_specification_impl(ctx):
    return [DefaultInfo(files = depset(ctx.files.srcs)), TrlcProviderInfo(spec = depset(ctx.files.srcs))]

_trlc_specification = rule(
    implementation = _trlc_specification_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = [".rsl"]),
    },
)

def trlc_specification(**kwargs):
    _trlc_specification(**kwargs)

def trlc_specification_test(name, reqs, srcs = ["@trlc//:trlc.py"], main = "trlc.py", **kwargs):
    native.py_test(
        name = name,
        srcs = srcs,
        args = ["--use-cvc5-binary $(location @trlc//:cvc5)", "--verify", "--skip-trlc-files"],
        main = main,
        deps = ["@trlc//trlc:trlc"],
        data = ["@trlc//:cvc5"] + reqs,
    )

def _trlc_requirement_impl(ctx):
    transitive_spec = []
    transitive_reqs = []
    for dep in ctx.attr.deps:
        trlc_provider = dep[TrlcProviderInfo]
        transitive_spec.append(trlc_provider.spec)
        transitive_reqs.append(trlc_provider.reqs)

    own_specs = ctx.files.spec if hasattr(ctx.files, "spec") else []

    return [
        DefaultInfo(
            files = depset(ctx.files.srcs, transitive = transitive_reqs + transitive_spec + [depset(own_specs)])
        ),
        TrlcProviderInfo(
            spec = depset(own_specs, transitive = transitive_spec),
            reqs = depset(ctx.files.srcs, transitive = transitive_reqs),
        ),
    ]

_trlc_requirement = rule(
    implementation = _trlc_requirement_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = [".trlc"]),
        "deps": attr.label_list(allow_files = False, allow_empty = True, providers = [TrlcProviderInfo]),
        "spec": attr.label_list(allow_empty = True, providers = [DefaultInfo]),
    },
)

def trlc_requirements(**kwargs):
    _trlc_requirement(**kwargs)

def trlc_requirements_test(name, reqs, srcs = ["@trlc//:trlc.py"], main = "trlc.py", **kwargs):
    native.py_test(
        name = name,
        srcs = srcs,
        args = ["--use-cvc5-binary $(location @trlc//:cvc5)", "--verify"],
        main = main,
        deps = ["@trlc//trlc:trlc"],
        data = ["@trlc//:cvc5"] + reqs,
    )
