# Copilot Instructions for TRLC (Starter)

Use these instructions for any work in this repository.

## Project profile

- Repository: TRLC (Treat Requirements Like Code), Python reference
  implementation plus docs and Bazel integration.
- Priorities: language correctness, deterministic behavior, and keeping spec/docs/tests aligned.
- Runtime constraints: Python 3.8–3.14 supported.

## Default workflow

1. Read nearby docs before changing behavior:
   - `documentation/architecture.md`
   - `documentation/dev_setup.md`
   - `documentation/LRM.md` and `language-reference-manual/` for language-level changes
2. Prefer small, focused patches that solve root causes.
3. Prefer the target style below, even when surrounding code uses older patterns.
4. Introduce style migration incrementally in touched areas; avoid
  broad no-op rewrites.

## Target style migration policy

Adopt the following style over time in production code:

- No `assert` statements for runtime behavior checks in production
  paths; use explicit validation and errors.
- Prefer f-strings over `%` formatting and `.format(...)` for string interpolation.
- Do not use horizontal alignment for assignments, dict colons, or
  similar layout; use regular Python spacing instead.
- Prefer smaller files and split toward one file per class where practical.
- Format code according to Black-compatible conventions.
- Class names shall no longer follow the Ada naming convention, but
  shall be in PascalCase (e.g., `MyClass`).
- Function and method names shall be in snake_case (e.g., `my_function`).

Legacy TRLC code used runtime `assert` checks heavily; migrate away
incrementally by replacing them with explicit validation and proper
error handling in touched code.

When changing existing code, apply these rules in the edited scope where safe.
Old code may remain in legacy style until it is touched for other reasons.

## Environment and commands

Repo is migrating Make→Bazel: prefer Bazel; use Make only if no Bazel target exists.

## Change policy by area

### Python implementation (`trlc/`, `trlc.py`, utilities)

- Add or update tests for behavior changes (unit and/or system tests as appropriate).
- Preserve existing public API and CLI semantics unless task explicitly
  requires a breaking change.
- Keep error messages and diagnostics stable where feasible (many tests assert exact output).

### Language and checker behavior

- If language semantics change, update both:
  - language reference/manual sources in `language-reference-manual/` and/or `documentation/`
  - relevant tests and expected outputs
- Keep code, docs, and traceability artifacts logically in sync in the same change.

## Guardrails

- Do not edit generated artifacts unless explicitly requested (for
  example `docs/` HTML output files).
- Do not introduce new dependencies unless necessary; if added, update
  the appropriate requirements files.
- Avoid broad renames/moves unless the task specifically asks for structural changes.
- Keep commits/patches atomic: code + tests + docs that belong to the
  same behavior change.

## Expected Copilot output style

- Explain assumptions briefly when requirements are ambiguous.
- Propose the smallest safe implementation first.
- After edits, run the narrowest relevant checks first, then broader checks if needed.
