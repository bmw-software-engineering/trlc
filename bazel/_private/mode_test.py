"""System test runner – runs all modes for one test directory.

Arguments are supplied by the ``trlc_system_test`` / ``trlc_partial_test``
macro via Bazel ``args`` on the ``py_test`` target:

  sys.argv[1]  root_dir   -- workspace-relative path of the test root,
                             e.g. "tests-system" or "tests-large-partial"
  sys.argv[2]  test_dir   -- subdirectory name within root_dir
  sys.argv[3]  cvc5_rloc  -- runfiles-relative path of the cvc5 binary

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
_CVC5_RLOC = sys.argv[3]


def _srcdir(*parts):
    """Resolve a path inside the runfiles tree via TEST_SRCDIR."""
    workspace = os.environ.get("TEST_WORKSPACE", "_main")
    return os.path.join(os.environ["TEST_SRCDIR"], workspace, *parts)


def _get_modes():
    """Return the list of modes to run, derived from golden files present."""
    test_src = _srcdir(_ROOT_DIR, _TEST_DIR)
    return sorted(f for f in os.listdir(test_src) if f.startswith("output"))


def _get_extra_args():
    """Return extra trlc flags from the optional ``options`` file, or ``[]``."""
    options_path = _srcdir(_ROOT_DIR, _TEST_DIR, "options")
    if os.path.isfile(options_path):
        with open(options_path, encoding="UTF-8") as fh:
            return fh.read().split()
    return []


def _run_mode(mode):
    """Run trlc for *mode* and return a diff string, or None on success."""
    # Import inside the function so that coverage instruments trlc.
    from trlc.trlc import trlc  # noqa: PLC0415

    root = _srcdir(_ROOT_DIR)
    sources = _srcdir(_ROOT_DIR, _TEST_DIR) + os.sep
    golden_path = _srcdir(_ROOT_DIR, _TEST_DIR, mode)
    actual_path = os.path.join(os.environ["TEST_TMPDIR"], "actual_" + mode)

    # chdir to root so that relative paths in options files (e.g.
    # "large/pkg.trlc" in tests-large-partial) resolve correctly.
    os.chdir(root)

    args = ["trlc"]

    if mode == "output":
        args += ["--verify"]
    elif mode == "output.smtlib":
        # _CVC5_RLOC is a runfiles-relative path produced by
        # $(rlocationpath //:cvc5); resolve it via TEST_SRCDIR directly.
        cvc5 = os.path.join(os.environ["TEST_SRCDIR"], _CVC5_RLOC)
        args += ["--verify", "--use-cvc5-binary", cvc5]
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
