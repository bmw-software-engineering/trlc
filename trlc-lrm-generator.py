#!/usr/bin/env python3
#
# TRLC - Treat Requirements Like Code
# Copyright (C) 2022 Florian Schanda
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

from trlc.errors import Message_Handler
from trlc.trlc import Source_Manager
from trlc.lexer import Token
from trlc import ast
import sys
import os
import html
import re


class BNF_Token:
    def __init__(self,  source, kind, value):
        assert isinstance(source, Token)


class BNF_Lexer:
    def __init__(self, fragment):
        assert isinstance(fragment, str)
        self.fragment = fragment


def write_heading(fd, name, depth):
    fd.write("<h%u>%s</h%u>\n" % (depth,
                                  html.escape(name),
                                  depth))
def write_header(fd):
    fd.write("<!DOCTYPE html>\n")
    fd.write("<html>\n")
    fd.write("<head>\n")
    fd.write("<title>TRLC Language Reference Manual</title>\n")
    fd.write("</head>\n")
    fd.write("<body>\n")
    write_heading(fd, "TRLC Language Reference Manual", 1)

def write_footer(fd):
    fd.write("<hr>\n")
    fd.write("<div>Generated by trlc-lrm-generator.py</div>\n")
    fd.write("</body>\n")
    fd.write("</html>\n")

def section_list(section):
    assert isinstance(section, ast.Section)
    if section.parent:
        return section_list(section.parent) + [section.name]
    else:
        return [section.name]

def section_depth(section):
    assert isinstance(section, ast.Section)
    if section.parent:
        return section_depth(section.parent) + 1
    else:
        return 1

def fmt_text(text):
    text = " ".join(text.replace("\n", " ").split())
    text = html.escape(text)
    text = re.sub("`(.*?)`", "<tt>\\1</tt>", text)
    return text

def write_text_object(fd, obj, context):
    data = obj.to_python_dict()

    # Build current section
    if obj.section:
        new_section = section_list(obj.section)
    else:
        new_section = []

    if obj.e_typ.name in ("Text", "Grammar",
                          "Terminal",
                          "Keywords",
                          "Punctuation"):
        pass
    elif obj.e_typ.name == "Semantics":
        new_section.append(data["kind"] + " Semantics")
    elif obj.e_typ.name == "Recommendation":
        new_section.append("Implementation Recommendation")
    elif obj.e_typ.name == "Example":
        new_section.append("Example")
    else:
        assert False

    # Generate new headings as appropriate
    if context["old_section"] is not None:
        old_section = context["old_section"]
    else:
        old_section = []
    identical = True
    for idx, heading in enumerate(new_section):
        if idx < len(old_section):
            if heading != old_section[idx]:
                identical = False
        else:
            identical = False
        if not identical:
            write_heading(fd, heading, idx + 2)

    # Store new section
    context["old_section"] = new_section

    # Emit
    fd.write("<div>\n")
    if data["text"]:
        fd.write(fmt_text(data["text"]) + "\n")
    if data["bullets"]:
        fd.write("<ul>\n")
        for item in data["bullets"]:
            fd.write("  <li>%s</li>\n" % fmt_text(item))
        fd.write("</ul>\n")
    fd.write("</div>\n")
    if obj.e_typ.name == "Terminal":
        fd.write("<div>")
        fd.write("<code>%s</code>\n" % data["def"])
        fd.write("</div>\n")
    elif obj.e_typ.name == "Grammar":
        fd.write("<div>")
        fd.write("<pre>%s</pre>\n" % data["bnf"])
        fd.write("</div>\n")


def main():
    mh = Message_Handler()
    sm = Source_Manager(mh)

    sm.register_directory("language-reference-manual")
    symbols = sm.process()
    if symbols is None:
        sys.exit(1)

    pkg_lrm = symbols.lookup_assuming(mh, "LRM", ast.Package)
    obj_license = None
    typ_text = pkg_lrm.symbols.lookup_assuming(mh, "Text", ast.Record_Type)
    typ_gram = pkg_lrm.symbols.lookup_assuming(mh, "Grammar", ast.Record_Type)

    context = {
        "old_section": None
    }
    with open("docs/lrm.html", "w") as fd:
        write_header(fd)
        for obj in pkg_lrm.symbols.iter_record_objects():
            if obj.e_typ.is_subclass_of(typ_text):
                write_text_object(fd, obj, context)
        write_footer(fd)

if __name__ == "__main__":
    main()
