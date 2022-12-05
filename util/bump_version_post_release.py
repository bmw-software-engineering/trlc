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

import os

import util.changelog

from trlc.version import VERSION_TUPLE

major, minor, release = VERSION_TUPLE
release += 1

# Bump version and update version.py

VERSION_FILE = os.path.join("trlc", "version.py")

tmp = ""
with open(VERSION_FILE, "r") as fd:
    for raw_line in fd:
        if raw_line.startswith("VERSION_TUPLE"):
            raw_line = 'VERSION_TUPLE = (%u, %u, %u)\n' % (major,
                                                           minor,
                                                           release)
        elif raw_line.startswith("VERSION_SUFFIX"):
            raw_line = 'VERSION_SUFFIX = "dev"\n'

        tmp += raw_line
with open(VERSION_FILE, "w") as fd:
    fd.write(tmp)

TRLC_VERSION = "%u.%u.%u-dev" % (major, minor, release)

# Update changelog and docs, adding a new entry

util.changelog.add_new_section(TRLC_VERSION)

# Assemble commit

os.system("git add trlc/version.py CHANGELOG.md")
os.system('git commit -m "Bump version to %s after release"' % TRLC_VERSION)
