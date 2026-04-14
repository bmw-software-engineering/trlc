"""Golden-file integration test runner for trlc_rst.

Runs TRLCRST against the input files in a test directory and diffs the
generated RST output against a golden ``output.rst`` file.

Arguments are supplied by the ``trlc_rst_integration_test`` macro via
Bazel ``args`` on the ``py_test`` target:

  sys.argv[1]  root_dir  -- workspace-relative path of the test root,
                            e.g. "tools/trlc_rst/tests"
  sys.argv[2]  test_dir  -- subdirectory name within root_dir,
                            e.g. "simple-flat"

Path resolution uses standard Bazel test environment variables:

  TEST_SRCDIR   -- absolute path to the base of the runfiles tree (required)
  TEST_WORKSPACE -- local repository workspace name               (optional)
  TEST_TMPDIR   -- private writable directory for test output     (required)
"""

import difflib
import os
import sys


def _srcdir(*parts):
    workspace = os.environ.get("TEST_WORKSPACE", "_main")
    return os.path.join(os.environ["TEST_SRCDIR"], workspace, *parts)


def _run(root_dir, test_dir):
    from trlc_rst import TRLCRST  # noqa: PLC0415

    test_src = _srcdir(root_dir, test_dir)
    golden_path = _srcdir(root_dir, test_dir, "output.rst")
    actual_path = os.path.join(os.environ["TEST_TMPDIR"], "output.rst")

    renderer = TRLCRST(test_src)
    renderer.render(actual_path)

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
            fromfile="golden (%s/output.rst)" % test_dir,
            tofile="actual",
        )
    )


if __name__ == "__main__":
    root_dir = sys.argv[1]
    test_dir = sys.argv[2]
    diff = _run(root_dir, test_dir)
    if diff is not None:
        print(diff, file=sys.stderr)
        sys.exit(1)
