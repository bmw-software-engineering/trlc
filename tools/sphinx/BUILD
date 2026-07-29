load("@rules_python//python:pip.bzl", "compile_pip_requirements")

# Run: bazel run //tools/sphinx:requirements_3_XX.update  --@@rules_python+//python/config_settings:python_version=3.XX
[
    compile_pip_requirements(
        name = "requirements_3_{}".format(version),
        src = "requirements.txt.in",
        python_version = "3.{}".format(version),
        requirements_txt = "requirements_3_{}.txt".format(version),
    )
    for version in [
        "9",
        "10",
        "11",
        "12",
    ]
]
