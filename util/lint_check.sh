#!/bin/bash
# Wrapper to run pylint on TRLC sources

set -euo pipefail

exec python3 -m pylint --rcfile=pylint3.cfg \
    --reports=no \
    trlc trlc*.py lobster-*.py
