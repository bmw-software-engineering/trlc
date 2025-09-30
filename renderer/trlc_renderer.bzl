def _trlc_renderer_impl(ctx):
    rendered_file = ctx.actions.declare_file("{}.rst".format(ctx.attr.name))
    args = ctx.actions.args()
    args.add("--output", rendered_file.path)

    # Add the mapping file from the filegroup
    for req in ctx.files.reqs:
        if req.basename == "mapping.json":
            args.add("--mapping", req.path)

    ctx.actions.run(
        inputs = ctx.files.reqs,
        outputs = [rendered_file],
        arguments = [args],
        executable = ctx.executable._renderer,
    )

    return [DefaultInfo(files = depset([rendered_file]))]

trlc_renderer = rule(
    implementation = _trlc_renderer_impl,
    attrs = {
        "reqs": attr.label_list(allow_files = True),
        "_renderer": attr.label(
            default = Label("@trlc//renderer:trlc_renderer"),
            executable = True,
            allow_files = True,
            cfg = "exec",
        ),
    },
)
