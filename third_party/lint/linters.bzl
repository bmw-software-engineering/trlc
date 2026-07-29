"Python linter aspects for trlc"

load("@aspect_rules_lint//lint:lint_test.bzl", "lint_test")
load("@aspect_rules_lint//lint:pylint.bzl", "lint_pylint_aspect")
load("@aspect_rules_lint//lint:ty.bzl", "lint_ty_aspect")

pylint = lint_pylint_aspect(
    binary = Label("//third_party/lint:pylint"),
    config = Label("//:pyproject.toml"),
)

pylint_test = lint_test(aspect = pylint)

ty = lint_ty_aspect(
    binary = Label("@aspect_rules_lint//lint:ty_bin"),
    config = Label("//:pyproject.toml"),
)

ty_test = lint_test(aspect = ty)
