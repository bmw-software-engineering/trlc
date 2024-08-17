#!/usr/bin/env python3

import re
import sys
import setuptools

from trlc import version

with open("README.md", "r") as fd:
    long_description = fd.read()

# For the readme to look right on PyPI we need to translate any
# relative links to absolute links to github.
fixes = []
for match in re.finditer(r"\[(.*)\]\((.*)\)", long_description):
    if not match.group(2).startswith("http"):
        fixes.append((match.span(0)[0], match.span(0)[1],
                      "[%s](%s/blob/main/%s)" % (match.group(1),
                                                 version.GITHUB_PROJECT,
                                                 match.group(2))))

for begin, end, text in reversed(fixes):
    long_description = (long_description[:begin] +
                        text +
                        long_description[end:])

project_urls = {
    "Bug Tracker"   : version.BUGS_URL,
    "Documentation" : version.DOCS_URL,
    "Source Code"   : version.CODE_URL,
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
    install_requires="PyVCG[api]==1.0.7",
    python_requires=">=3.8, <3.13",
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
