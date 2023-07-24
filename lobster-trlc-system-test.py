#!/usr/bin/env python3
#
# lobster-trlc-system-test - Extract tracing tags for LOBSTER
# Copyright (C) 2023 Bayerische Motoren Werke Aktiengesellschaft (BMW AG)
#
# This component of TRLC program is free software: you can
# redistribute it and/or modify it under the terms of the GNU Affero
# General Public License as published by the Free Software Foundation,
# either version 3 of the License, or (at your option) any later
# version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
# Affero General Public License for more details.
#
# You should have received a copy of the GNU Affero General Public
# License along with this program. If not, see
# <https://www.gnu.org/licenses/>.

import os
import sys

from lobster.items import Tracing_Tag, Activity
from lobster.location import File_Reference
from lobster.io import lobster_write


TEST_DIR = "tests"
TARGET   = "system-tests.lobster"


def process(testname):
    test_dir = os.path.join(TEST_DIR, testname)
    assert os.path.isdir(test_dir)

    tag_file = os.path.join(test_dir, "tracing")

    item = Activity(
        tag       = Tracing_Tag(namespace = "trlc-st",
                                tag       = testname),
        location  = File_Reference(filename = test_dir),
        framework = "TRLCST",
        kind      = "Test Directory")

    if os.path.isfile(tag_file):
        with open(tag_file, "r", encoding="UTF-8") as fd:
            tags = [Tracing_Tag(namespace = "req",
                                tag       = line.strip())
                    for line in fd.read().splitlines()
                    if line.strip()]
        for tag in tags:
            item.add_tracing_target(tag)

    return item


def main():
    items = []
    for dirent in sorted(os.scandir(TEST_DIR),
                         key=lambda de: de.name):
        if dirent.is_dir():
            if dirent.name == "htmlcov":
                continue
            items.append(process(dirent.name))

    with open(TARGET, "w", encoding="UTF-8") as fd:
        lobster_write(fd, Activity, "lobster-trlc-system-test", items)

    print("Written %u items to %s" % (len(items), TARGET))
    return 0


if __name__ == "__main__":
    sys.exit(main())
