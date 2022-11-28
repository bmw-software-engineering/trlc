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

# This helper script tags a release using the GitHub API.
#
# https://docs.github.com/en/rest/reference/repos#create-a-release

import os
import sys
import json

import requests

from trlc.version import TRLC_VERSION
import util.changelog

def main():
    username = os.environ.get("GITHUB_USERNAME", None)
    if username is None:
        print("Please set the GITHUB_USERNAME environment variable")

    token = os.environ.get("GITHUB_TRLC_TOKEN", None)
    if token is None:
        print("Please set the GITHUB_TRLC_TOKEN environment variable")

    if username is None or token is None:
        sys.exit(1)

    auth = requests.auth.HTTPBasicAuth(username, token)

    api_endpoint = "https://api.github.com/repos/%s/%s/releases" % \
        ("bmw_software_engineering", "trlc")

    tag_name = TRLC_VERSION
    rel_name = "Release %s" % TRLC_VERSION
    rel_body = "### %s\n\n%s" % (TRLC_VERSION, util.changelog.current_section())

    data = {"tag_name" : tag_name,
            "name"     : rel_name,
            "body"     : rel_body}

    r = requests.post(api_endpoint, auth=auth, data=json.dumps(data))
    print(r)

if __name__ == "__main__":
    main()
