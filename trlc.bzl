def _trlc_specification_impl(ctx):
    return DefaultInfo(files = depset(ctx.files.srcs))

_trlc_specification = rule(
    implementation = _trlc_specification_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = [".rsl"]),
    },
)

def trlc_specification(**kwargs):
    _trlc_specification(**kwargs)

def _trlc_requirement_impl(ctx):
    depending_files = []
    for spec in ctx.attr.spec:
        depending_files.append(spec[DefaultInfo].files)

    return DefaultInfo(files = depset(ctx.files.srcs, transitive = depending_files))

_trlc_requirement = rule(
    implementation = _trlc_requirement_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = [".trlc"]),
        "spec": attr.label_list(allow_empty = False, providers = [DefaultInfo]),
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
