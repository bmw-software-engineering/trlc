TrlcProviderInfo = provider(
    fields = {
        "spec": "Holds the specification files (*.rsl) including transitive",
        "reqs": "Holds only the direct requirement files (*.trlc) from srcs",
        "deps": "Holds only the transitive requirement files (*.trlc) from deps",
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
        args = ["--verify", "--skip-trlc-files"] +
               ["$(locations %s)" % req for req in reqs],
        main = main,
        deps = ["@trlc//trlc:trlc"],
        data = ["@trlc//:cvc5"] + reqs,
        **kwargs
    )

def _trlc_requirement_impl(ctx):
    transitive_spec = []
    transitive_reqs = []
    for dep in ctx.attr.deps:
        trlc_provider = dep[TrlcProviderInfo]
        transitive_spec.append(trlc_provider.spec)
        transitive_reqs.append(trlc_provider.reqs)
        transitive_reqs.append(trlc_provider.deps)

    own_specs = depset(transitive = [
        spec_target[DefaultInfo].files
        for spec_target in ctx.attr.spec
    ])

    return [
        DefaultInfo(
            files = depset(ctx.files.srcs, transitive = transitive_reqs + transitive_spec + [own_specs]),
        ),
        TrlcProviderInfo(
            spec = depset(transitive = [own_specs] + transitive_spec),
            reqs = depset(ctx.files.srcs),
            deps = depset(transitive = transitive_reqs),
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
        args = ["--verify"] +
               ["$(locations %s)" % req for req in reqs],
        main = main,
        deps = ["@trlc//trlc:trlc"],
        data = ["@trlc//:cvc5"] + reqs,
        **kwargs
    )
