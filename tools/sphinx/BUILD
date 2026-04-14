load("@rules_python//python:pip.bzl", "compile_pip_requirements")

# Run: bazel run //tools/sphinx:requirements.update
compile_pip_requirements(
    name = "requirements",
    src = "requirements.txt.in",
    requirements_txt = "requirements.txt",
)
