#!/usr/bin/env python3
"""Wrapper to run pycodestyle on TRLC sources."""

import subprocess
import sys

DEFAULT_TARGETS = [
    "trlc",
    "trlc.py",
    "trlc-lrm-generator.py",
    "lobster-trlc-system-test.py",
]


targets = sys.argv[1:] or DEFAULT_TARGETS
result = subprocess.run([sys.executable, "-m", "pycodestyle", *targets], cwd=".")
sys.exit(result.returncode)
