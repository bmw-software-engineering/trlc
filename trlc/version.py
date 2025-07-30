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

VERSION_TUPLE = (2, 0, 2)
VERSION_SUFFIX = ""

TRLC_VERSION = ("%u.%u.%u" % VERSION_TUPLE) + \
    ("-%s" % VERSION_SUFFIX if VERSION_SUFFIX else "")

FULL_NAME = "TRLC %s" % TRLC_VERSION

GITHUB_PROJECT = "https://github.com/bmw-software-engineering/trlc"
BUGS_URL = "%s/issues" % GITHUB_PROJECT
DOCS_URL = "%s#documentation" % GITHUB_PROJECT
CODE_URL = GITHUB_PROJECT
