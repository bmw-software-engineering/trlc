#!/usr/bin/env python3
#
# TRLC - Treat Requirements Like Code
# Copyright (C) 2024 Florian Schanda
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

# This utility script fetches and unpacks CVC5 binaries for use in CI.

import os
import urllib.request
import io
import zipfile
import argparse
import stat

CVC5_RELEASES = "http://github.com/cvc5/cvc5/releases/download"
CVC5_BINARY = "cvc5"
CVC5_EXECUTABLE = True

ap = argparse.ArgumentParser()
ap.add_argument("version")
ap.add_argument("platform")

options = ap.parse_args()

CVC5_VERSION = options.version

if options.platform == "linux":
    CVC5_PLATFORM = "Linux-x86_64-static"
elif options.platform == "osx13":
    CVC5_PLATFORM = "macOS-x86_64-static"
elif options.platform == "osx14":
    CVC5_PLATFORM = "macOS-arm64-static"
elif options.platform == "windows":
    CVC5_PLATFORM = "Win64-x86_64-static"
    CVC5_BINARY = "cvc5.exe"
    CVC5_EXECUTABLE = False
else:
    ap.error("unknown platform")

print ("Downloading CVC5 archive (%s, %s)" % (CVC5_VERSION, CVC5_PLATFORM))
with urllib.request.urlopen("%s/cvc5-%s/cvc5-%s.zip" %
                            (CVC5_RELEASES,
                             CVC5_VERSION,
                             CVC5_PLATFORM)) as fd:
    content = fd.read()

print ("Extracting %s" % CVC5_BINARY)
with zipfile.ZipFile(io.BytesIO(content)) as zf:
    with zf.open("cvc5-%s/bin/%s" % (CVC5_PLATFORM,
                                     CVC5_BINARY)) as fd:
        with open(CVC5_BINARY, "wb") as fd_out:
            fd_out.write(fd.read())

if CVC5_EXECUTABLE:
    print("Setting executable bit")
    os.chmod(CVC5_BINARY, stat.S_IRUSR | stat.S_IWUSR | stat.S_IXUSR)
