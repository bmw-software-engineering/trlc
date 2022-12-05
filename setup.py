#!/usr/bin/env python3

import sys
import setuptools

from trlc import version

with open("README.md", "r") as fd:
    long_description = fd.read()

gh_root = "https://github.com"
gh_project = "bmw-software-engineering/trlc"

project_urls = {
    "Bug Tracker"   : "%s/%s/issues" % (gh_root, gh_project),
    "Documentation" : "%s/pages/%s/" % (gh_root, gh_project),
    "Source Code"   : "%s/%s"        % (gh_root, gh_project),
}

setuptools.setup(
    name="trlc",
    version=version.TRLC_VERSION,
    author="Bayerische Motoren Werke Aktiengesellschaft (BMW AG)",
    author_email="florian.schanda@bmw.de",
    description="Treat Requirements Like Code",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url=project_urls["Source Code"],
    project_urls=project_urls,
    license="GNU General Public License v3",
    packages=setuptools.find_packages(),
    # install_requires=["cvc5>=1.0.1"],
    python_requires=">=3.7, <4",
    classifiers=[
        "Development Status :: 5 - Production/Stable",
        "Environment :: Console",
        "Intended Audience :: Developers",
        "License :: OSI Approved :: GNU General Public License v3 or later (GPLv3+)",
        "Topic :: Documentation",
        "Topic :: Software Development",
    ],
    entry_points={
        "console_scripts": [
            "trlc = trlc.trlc:main",
        ],
    },
)
