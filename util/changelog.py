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

# Various utilities to query / manipulate CHANGELOG.md


def current_section():
    """ Get most recent (i.e. first) section of the changelog """
    tmp = ""
    relevant_log = ""
    mode = "searching for changelog"
    with open("CHANGELOG.md", "r") as fd:
        for raw_line in fd:
            if mode == "searching for changelog":
                if raw_line.startswith("## Changelog"):
                    mode = "searching for first entry"
            elif mode == "searching for first entry":
                if raw_line.startswith("### "):
                    mode = "eating log"
            elif mode == "eating log":
                if raw_line.startswith("### "):
                    mode = "done"
                else:
                    relevant_log += raw_line
            else:
                pass
            tmp += raw_line

    return relevant_log.strip()


def set_current_title(new_title):
    """ Update last CHANGELOG entry to the given title. """
    assert isinstance(new_title, str)

    tmp = ""
    mode = "searching for changelog"
    with open("CHANGELOG.md", "r") as fd:
        for raw_line in fd:
            if mode == "searching for changelog":
                if raw_line.startswith("## Changelog"):
                    mode = "searching for first entry"
            elif mode == "searching for first entry":
                if raw_line.startswith("### "):
                    raw_line = "### %s\n" % new_title
                    mode = "done"
            else:
                pass
            tmp += raw_line
    with open("CHANGELOG.md", "w") as fd:
        fd.write(tmp)


def add_new_section(new_title):
    """ Add new CHANGELOG entry with the given title. """
    assert isinstance(new_title, str)

    tmp = ""
    mode = "searching for changelog"
    with open("CHANGELOG.md", "r") as fd:
        for raw_line in fd:
            tmp += raw_line
            if mode == "searching for changelog":
                if raw_line.startswith("## Changelog"):
                    mode = "done"
                    tmp += "\n\n### %s\n\n" % new_title
            else:
                pass
    with open("CHANGELOG.md", "w") as fd:
        fd.write(tmp)
