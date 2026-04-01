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
            files = depset(ctx.files.srcs, transitive = transitive_reqs + transitive_spec + [own_specs])
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

################################
# TRLC RST
################################

def _trlc_rst_impl(ctx):
    rendered_file = ctx.actions.declare_file("{}.rst".format(ctx.attr.name))

    all_inputs = depset(transitive = [
        req[DefaultInfo].files
        for req in ctx.attr.reqs
    ] + [
        dep[DefaultInfo].files
        for dep in ctx.attr.deps
    ])

    source_files = depset(transitive = [
        req[TrlcProviderInfo].reqs
        for req in ctx.attr.reqs
    ])

    dep_files = depset(transitive = [
        req[TrlcProviderInfo].spec
        for req in ctx.attr.reqs
    ] + [
        req[TrlcProviderInfo].deps
        for req in ctx.attr.reqs
    ] + [
        dep[TrlcProviderInfo].reqs
        for dep in ctx.attr.deps
    ] + [
        dep[TrlcProviderInfo].spec
        for dep in ctx.attr.deps
    ] + [
        dep[TrlcProviderInfo].deps
        for dep in ctx.attr.deps
    ])

    args = ctx.actions.args()
    args.add("--output", rendered_file.path)
    args.add("--title", ctx.attr.title)
    args.add_all("--dep-files", dep_files)
    args.add_all("--source-files", source_files)

    ctx.actions.run(
        inputs = all_inputs,
        outputs = [rendered_file],
        arguments = [args],
        executable = ctx.executable._renderer,
    )

    return [DefaultInfo(files = depset([rendered_file]))]

_trlc_rst = rule(
    implementation = _trlc_rst_impl,
    attrs = {
        "reqs": attr.label_list(
            providers = [TrlcProviderInfo],
            doc = "trlc_requirements targets whose record objects are rendered.",
        ),
        "deps": attr.label_list(
            providers = [TrlcProviderInfo],
            default = [],
            doc = "Additional trlc_requirements targets needed for dependency resolution only. Their record objects are not rendered.",
        ),
        "title": attr.string(default = "Requirements"),
        "_renderer": attr.label(
            default = Label("//tools/trlc_rst:trlc_rst"),
            executable = True,
            allow_files = True,
            cfg = "exec",
        ),
    },
)

def trlc_rst(name, reqs, deps = [], title = "Requirements", **kwargs):
    _trlc_rst(
        name = name,
        reqs = reqs,
        deps = deps,
        title = title,
        **kwargs
    )
