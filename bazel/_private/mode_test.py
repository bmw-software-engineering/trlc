"""System test runner – runs all modes for one test directory.

Arguments are supplied by the ``trlc_system_test`` / ``trlc_partial_test``
macro via Bazel ``args`` on the ``py_test`` target:

  sys.argv[1]  root_dir   -- workspace-relative path of the test root,
                             e.g. "tests-system" or "tests-large-partial"
  sys.argv[2]  test_dir   -- subdirectory name within root_dir

Available modes are discovered at runtime by listing the ``output*`` golden
files present in the test directory.  An optional ``options`` file in the
directory may supply extra trlc flags (whitespace-separated), e.g.
``--no-detailed-info`` or source paths for partial-loading tests.

Path resolution uses only standard Bazel test environment variables
(https://bazel.build/reference/test-encyclopedia):

  TEST_SRCDIR    -- absolute path to the base of the runfiles tree (required)
  TEST_WORKSPACE -- local repository workspace name               (optional)
  TEST_TMPDIR    -- private writable directory for test output     (required)
"""

import difflib
import os
import sys

_ROOT_DIR = sys.argv[1]
_TEST_DIR = sys.argv[2]
_MANIFEST = None


def _runfile_key(*parts):
    """Return a manifest key under TEST_WORKSPACE using forward slashes."""
    workspace = os.environ.get("TEST_WORKSPACE", "_main")
    return "/".join([workspace] + list(parts))


def _load_manifest():
    """Load RUNFILES manifest into a dict, or return {} when unavailable."""
    global _MANIFEST  # noqa: PLW0603
    if _MANIFEST is not None:
        return _MANIFEST

    manifest_path = os.environ.get("RUNFILES_MANIFEST_FILE")
    if not manifest_path:
        candidate = os.path.join(os.environ["TEST_SRCDIR"], "MANIFEST")
        if os.path.isfile(candidate):
            manifest_path = candidate

    manifest = {}
    if manifest_path and os.path.isfile(manifest_path):
        with open(manifest_path, encoding="UTF-8") as fh:
            for line in fh:
                line = line.rstrip("\n")
                if not line:
                    continue
                key, sep, value = line.partition(" ")
                if sep:
                    manifest[key] = value

    _MANIFEST = manifest
    return _MANIFEST


def _debug_dump():
    """Return a compact debug dump for runfiles resolution failures."""
    srcdir = os.environ.get("TEST_SRCDIR", "<unset>")
    workspace = os.environ.get("TEST_WORKSPACE", "<unset>")
    debug = [
        "TEST_SRCDIR=%s" % srcdir,
        "TEST_WORKSPACE=%s" % workspace,
        "_ROOT_DIR=%s" % _ROOT_DIR,
        "_TEST_DIR=%s" % _TEST_DIR,
    ]

    if os.path.isdir(srcdir):
        debug.append("Contents of TEST_SRCDIR:")
        for entry in sorted(os.listdir(srcdir))[:20]:
            debug.append("  %s" % entry)
        workspace_dir = os.path.join(srcdir, workspace)
        if os.path.isdir(workspace_dir):
            debug.append("Contents of %s:" % workspace)
            for entry in sorted(os.listdir(workspace_dir))[:20]:
                debug.append("  %s" % entry)

    debug.append("RUNFILES_MANIFEST_FILE=%s" % os.environ.get("RUNFILES_MANIFEST_FILE", "<unset>"))
    debug.append("MANIFEST entries loaded=%d" % len(_load_manifest()))
    return "\n".join(debug)


def _resolve_file(*parts):
    """Resolve a runfile path to a real filesystem path."""
    direct = _srcdir(*parts)
    if os.path.exists(direct):
        return direct

    manifest_value = _load_manifest().get(_runfile_key(*parts))
    if manifest_value and os.path.exists(manifest_value):
        return manifest_value

    raise FileNotFoundError(
        "Runfile not found: %s\n%s" % ("/".join(parts), _debug_dump())
    ) from None


def _resolve_dir(*parts):
    """Resolve a runfiles directory, including manifest-only Windows runs."""
    direct = _srcdir(*parts)
    if os.path.isdir(direct):
        return direct

    prefix = _runfile_key(*parts) + "/"
    for key, value in _load_manifest().items():
        if not key.startswith(prefix):
            continue
        tail = key[len(prefix):]
        if not tail:
            continue

        # Reconstruct the directory by removing tail segments from value.
        candidate = value
        for _ in tail.split("/"):
            candidate = os.path.dirname(candidate)
        if os.path.isdir(candidate):
            return candidate

    raise FileNotFoundError(
        "Runfiles directory not found: %s\n%s" % ("/".join(parts), _debug_dump())
    ) from None


def _srcdir(*parts):
    """Resolve a path inside the runfiles tree via TEST_SRCDIR."""
    workspace = os.environ.get("TEST_WORKSPACE", "_main")
    return os.path.join(os.environ["TEST_SRCDIR"], workspace, *parts)


def _get_modes():
    """Return the list of modes to run, derived from golden files present."""
    test_src = _resolve_dir(_ROOT_DIR, _TEST_DIR)
    return sorted(f for f in os.listdir(test_src) if f.startswith("output"))


def _get_extra_args():
    """Return extra trlc flags from the optional ``options`` file, or ``[]``."""
    try:
        options_path = _resolve_file(_ROOT_DIR, _TEST_DIR, "options")
    except FileNotFoundError:
        return []

    if os.path.isfile(options_path):
        with open(options_path, encoding="UTF-8") as fh:
            return fh.read().split()
    return []


def _run_mode(mode):
    """Run trlc for *mode* and return a diff string, or None on success."""
    # Import inside the function so that coverage instruments trlc.
    from trlc.trlc import trlc  # noqa: PLC0415

    root = _resolve_dir(_ROOT_DIR)
    sources = _resolve_dir(_ROOT_DIR, _TEST_DIR) + os.sep
    golden_path = _resolve_file(_ROOT_DIR, _TEST_DIR, mode)
    actual_path = os.path.join(os.environ["TEST_TMPDIR"], "actual_" + mode)

    # chdir to root so that relative paths in options files (e.g.
    # "large/pkg.trlc" in tests-large-partial) resolve correctly.
    os.chdir(root)

    args = ["trlc"]

    if mode in ("output", "output.smtlib"):
        args += ["--verify"]
    elif mode == "output.brief":
        args += ["--no-lint", "--brief"]
    elif mode == "output.json":
        args += ["--no-lint", "--debug-api-dump"]

    args.extend(_get_extra_args())
    args.append(sources)

    # Add logging configuration last so --log only consumes FILE and optional PREFIX.
    args.extend(["--log", actual_path, root + os.sep])

    sys.argv = args
    trlc()

    with open(actual_path, encoding="UTF-8") as fh:
        actual = fh.read()
    with open(golden_path, encoding="UTF-8") as fh:
        golden = fh.read()

    if actual == golden:
        return None
    return "".join(
        difflib.unified_diff(
            golden.splitlines(keepends=True),
            actual.splitlines(keepends=True),
            fromfile="golden (%s/%s)" % (_TEST_DIR, mode),
            tofile="actual",
        )
    )


failed = []
for _mode in _get_modes():
    diff = _run_mode(_mode)
    if diff is not None:
        print(diff, file=sys.stderr)
        failed.append(_mode)

if failed:
    print("FAILED modes: %s" % ", ".join(failed), file=sys.stderr)
    sys.exit(1)
