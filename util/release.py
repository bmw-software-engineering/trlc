#!/usr/bin/env python3
#
# TRLC - Treat Requirements Like Code
# Copyright (C) 2022 Bayerische Motoren Werke Aktiengesellschaft (BMW AG)
#
# This file is part of the TRLC Python Reference Implementation.
#
# TRLC is free software: you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# TRLC is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
# License for more details.
#
# You should have received a copy of the GNU General Public License
# along with TRLC. If not, see <https://www.gnu.org/licenses/>.

# Helper script to remove "-dev" from current version; update
# changelog/docs; and commit.

import os

import util.changelog

# Update version.py to remove the -dev (or if given) use a different
# version number.

tmp = ""
with open("trlc/version.py", "r") as fd:
    for raw_line in fd:
        if raw_line.startswith("VERSION_SUFFIX"):
            raw_line = 'VERSION_SUFFIX = ""\n'

        tmp += raw_line
with open("trlc/version.py", "w") as fd:
    fd.write(tmp)

from trlc.version import TRLC_VERSION
print(TRLC_VERSION)

# Update last CHANGELOG entry and documentation to use the new
# version.

util.changelog.set_current_title(TRLC_VERSION)
os.system("make doc")

# Commit & tag

os.system("git add CHANGELOG.md docs trlc/version.py")
os.system('git commit -m "Release %s"' % TRLC_VERSION)
