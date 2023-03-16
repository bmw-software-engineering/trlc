#!/usr/bin/env python3
#
# TRLC - Treat Requirements Like Code
# Copyright (C) 2022-2023 Florian Schanda
# Copyright (C) 2023 Bayerische Motoren Werke Aktiengesellschaft (BMW AG)
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

# pylint: disable=invalid-name

import sys
import html
import re
import os
import hashlib
from collections import OrderedDict

from trlc.errors import Message_Handler, TRLC_Error
from trlc.lexer import Source_Reference, TRLC_Lexer
from trlc.parser import Parser
from trlc.trlc import Source_Manager
from trlc import ast

BMW_BLUE_1 = "#0066B1"
BMW_BLUE_2 = "#003D78"
BMW_RED    = "#E22718"
BMW_GREY   = "#6f6f6f"
BMW_SILVER = "#d6d6d6"

EMACS_STRING = "#8d2153"


class BNF_Token:
    KIND = (
        "NONTERMINAL",     # foo   foo_NAME
        "TERMINAL",        # FOO   FOO_name
        "PRODUCTION",      # ::=
        "ALTERNATIVE",     # |
        "SYMBOL",          # 'potato'
        "S_BRA", "S_KET",  # []
        "C_BRA", "C_KET",  # {}
        "RULE_END",        # two or more newlines
    )

    def __init__(self, kind, value, start, end, location):
        assert kind in BNF_Token.KIND
        assert isinstance(start, int)
        assert isinstance(end, int) and start <= end
        assert isinstance(location, Source_Reference)

        self.kind     = kind
        self.value    = value
        self.location = location
        self.start    = start
        self.end      = end

    def __repr__(self):
        return "BNF_Token(%s, %s, <loc>)" % (self.kind, self.value)


class BNF_Lexer:
    def __init__(self, mh, fragment, original_location):
        assert isinstance(mh, Message_Handler)
        assert isinstance(fragment, str)
        assert isinstance(original_location, Source_Reference)
        self.mh                = mh
        self.fragment          = fragment
        self.original_location = original_location
        self.fragment_length   = len(self.fragment)

        self.lexpos  = -2
        self.line_no = 0
        self.col_no  = 0
        self.cc = None
        self.nc = None
        self.eof_token_generated = False

        self.advance()

    def advance(self):
        self.lexpos += 1
        if self.cc == "\n" or self.lexpos == 0:
            self.line_no += 1
            self.col_no = 0
        if self.nc is not None:
            self.col_no += 1
        self.cc = self.nc
        self.nc = (self.fragment[self.lexpos + 1]
                   if self.lexpos + 1 < self.fragment_length
                   else None)

    def token(self):
        # Skip whitespace and comments
        num_nl = 0
        start_pos  = self.lexpos
        start_line = self.line_no
        start_col  = self.col_no
        while self.nc and self.nc.isspace():
            self.advance()
            if self.cc == "\n":
                num_nl += 1
        if num_nl < 2:
            self.advance()

        if self.cc is None:
            if not self.eof_token_generated:
                self.eof_token_generated = True
                return BNF_Token(kind     = "RULE_END",
                                 value    = None,
                                 start    = self.lexpos,
                                 end      = self.lexpos,
                                 location = self.mk_location(start_line,
                                                             start_col,
                                                             self.lexpos,
                                                             self.lexpos))
            return None

        # If we have more than one empty line then this is the end of
        # a rule.
        if num_nl >= 2:
            return BNF_Token(kind     = "RULE_END",
                             value    = None,
                             start    = start_pos,
                             end      = self.lexpos,
                             location = self.mk_location(self.line_no,
                                                         start_col,
                                                         start_pos,
                                                         self.lexpos))

        start_pos  = self.lexpos
        start_line = self.line_no
        start_col  = self.col_no

        if self.cc == "[":
            kind = "S_BRA"

        elif self.cc == "]":
            kind = "S_KET"

        elif self.cc == "{":
            kind = "C_BRA"

        elif self.cc == "}":
            kind = "C_KET"

        elif self.cc == "|":
            kind = "ALTERNATIVE"

        elif self.cc == ":":
            kind = "PRODUCTION"
            self.advance()
            if self.cc != ":":
                self.lex_error("malformed ::= operator")
            self.advance()
            if self.cc != "=":
                self.lex_error("malformed ::= operator")

        elif self.cc.islower():
            # Either nonterm or nonterm_NAME
            kind = "NONTERMINAL"
            while self.nc and (self.nc.isalpha() or self.nc == "_"):
                self.advance()

        elif self.cc.isupper():
            # Either TERMINAL or TERMINAL_name
            kind = "TERMINAL"
            while self.nc and (self.nc.isalpha() or self.nc == "_"):
                self.advance()

        elif self.cc == "'":
            kind = "SYMBOL"
            while self.nc and self.nc != "'":
                self.advance()
            if self.nc is None:
                self.lex_error("unclosed token literal")
            self.advance()

        else:
            self.lex_error("unexpected character %s" % self.cc)

        end_pos  = self.lexpos
        raw_text = self.fragment[start_pos:end_pos + 1]

        if kind == "TERMINAL":
            t_kind = ""
            t_name = None
            in_kind = True
            for c in raw_text:
                if in_kind and c.islower():
                    assert t_kind.endswith("_")
                    t_kind = t_kind[:-1]
                    in_kind = False
                    t_name = c
                elif in_kind:
                    t_kind += c
                else:
                    t_name += c
            value = (t_kind, t_name)

        elif kind == "NONTERMINAL":
            t_prod = ""
            t_name = None
            in_prod = True
            for c in raw_text:
                if in_prod and c.isupper():
                    assert t_prod.endswith("_")
                    t_prod = t_prod[:-1]
                    in_prod = False
                    t_name = c
                elif in_prod:
                    t_prod += c
                else:
                    t_name += c
            value = (t_prod, t_name)

        elif kind == "SYMBOL":
            value = raw_text[1:-1]

        else:
            value = None

        return BNF_Token(kind     = kind,
                         value    = value,
                         start    = start_pos,
                         end      = end_pos,
                         location = self.mk_location(start_line,
                                                     start_col,
                                                     start_pos,
                                                     end_pos))

    def mk_location(self, start_line, start_col, start_pos, end_pos):
        sref = Source_Reference(
            lexer      = self.original_location.lexer,
            start_line = self.original_location.line_no + (start_line - 1),
            start_col  = (self.original_location.col_no + 3
                          if start_line == 1
                          else start_col),
            start_pos  = self.original_location.start_pos + 3 + start_pos,
            end_pos    = self.original_location.start_pos + 3 + end_pos)
        return sref

    def lex_error(self, message):
        self.mh.error(self.mk_location(self.line_no, self.col_no,
                                       self.lexpos, self.lexpos),
                      message)


class BNF_AST_Node:
    def __init__(self, location):
        assert isinstance(location, Source_Reference)
        self.location = location


class BNF_Expansion(BNF_AST_Node):
    pass


class BNF_Literal(BNF_Expansion):
    def __init__(self, location, kind, value, name=None):
        super().__init__(location)
        assert kind in ("TERMINAL",
                        "NONTERMINAL",
                        "SYMBOL")
        assert isinstance(value, str)
        assert isinstance(name, str) or name is None

        self.kind  = kind
        self.value = value
        self.name  = name

    def __str__(self):
        return self.value


class BNF_Optional(BNF_Expansion):
    def __init__(self, location, expansion):
        super().__init__(location)
        assert isinstance(expansion, BNF_Expansion)

        self.expansion = expansion

    def __str__(self):
        return "[ %s ]" % str(self.expansion)


class BNF_Zero_Or_More(BNF_Expansion):
    def __init__(self, location, expansion):
        super().__init__(location)
        assert isinstance(expansion, BNF_Expansion)

        self.expansion = expansion

    def __str__(self):
        return "{ %s }" % str(self.expansion)


class BNF_String(BNF_Expansion):
    def __init__(self, members):
        assert isinstance(members, list) and len(members) >= 2
        for member in members:
            assert isinstance(member, BNF_Expansion)
        super().__init__(members[0].location)

        self.members = members

    def __str__(self):
        return " ".join(map(str, self.members))


class BNF_Alternatives(BNF_Expansion):
    def __init__(self, members):
        assert isinstance(members, list) and len(members) >= 2
        for member in members:
            assert isinstance(member, BNF_Expansion)
        super().__init__(members[0].location)

        self.members = members

    def __str__(self):
        return " | ".join(map(str, self.members))


class BNF_Parser:
    def __init__(self, mh):
        assert isinstance(mh, Message_Handler)

        self.mh = mh

        # Lexer state
        self.current_lexer = None
        self.ct            = None
        self.nt            = None

        # Symbol table
        self.token_kinds = {}
        self.terminals   = set()
        self.productions = {}
        self.bundles     = {}

    def advance(self):
        assert self.current_lexer is not None

        self.ct = self.nt
        self.nt = self.current_lexer.token()

    def error(self, token, message):
        assert isinstance(token, BNF_Token)
        assert isinstance(message, str)

        self.mh.error(token.location, message)

    def peek(self, kind):
        assert kind in BNF_Token.KIND

        return self.nt and self.nt.kind == kind

    def match(self, kind):
        assert kind in BNF_Token.KIND

        if self.nt is None:
            self.error(self.ct, "expected %s, encountered EOS instead" % kind)
        elif self.nt.kind != kind:
            self.error(self.nt, "expected %s, encountered %s instead" %
                       (kind, self.nt.kind))

        self.advance()

    def sem(self):
        for production in self.productions:
            self.sem_production(production)

    def sem_production(self, production):
        n_exp = self.productions[production]

        self.sem_expansion(n_exp)

    def sem_expansion(self, n_exp):
        assert isinstance(n_exp, BNF_Expansion)

        if isinstance(n_exp, (BNF_Zero_Or_More,
                              BNF_Optional)):
            self.sem_expansion(n_exp.expansion)

        elif isinstance(n_exp, (BNF_String,
                                BNF_Alternatives)):
            for n_member in n_exp.members:
                self.sem_expansion(n_member)

        else:
            self.sem_literal(n_exp)

    def sem_literal(self, n_literal):
        assert isinstance(n_literal, BNF_Literal)

        if n_literal.kind == "SYMBOL":
            if n_literal.value not in self.terminals:
                self.mh.warning(n_literal.location,
                                "unknown terminal '%s'" % n_literal.value)

        elif n_literal.kind == "TERMINAL":
            if n_literal.value not in self.token_kinds:
                self.mh.warning(n_literal.location,
                                "unknown terminal %s" % n_literal.value)

        else:
            assert n_literal.kind == "NONTERMINAL"
            if n_literal.value not in self.productions:
                self.mh.warning(n_literal.location,
                                "unknown production %s" % n_literal.value)

    def register_terminal(self, obj):
        assert isinstance(obj, ast.String_Literal)

        if obj.value in self.terminals:
            self.mh.error(obj.location,
                          "duplicate definition of terminal")
        self.terminals.add(obj.value)

    def register_backtick_terminals(self, obj):
        assert isinstance(obj, ast.String_Literal)

        for match in re.finditer("`([^`]*)`", obj.value):
            terminal = match.group(1)
            if terminal:
                if terminal in self.terminals:
                    self.mh.error(obj.location,
                                  "duplicate definition of terminal '%s'" %
                                  terminal)
                else:
                    self.terminals.add(terminal)
            else:
                self.mh.error(obj.location,
                              "empty terminal is not permitted")

    def register_token(self, obj, examples):
        assert isinstance(obj, ast.String_Literal)
        assert isinstance(examples, ast.Array_Aggregate)

        match = re.match("([A-Z_]+) *::= *(.*)", obj.value)
        if match is None:
            self.mh.error(obj.location,
                          "malformed token definition")

        if match.group(1) in self.token_kinds:
            self.mh.error(obj.location,
                          "duplicate definition of %s" % match.group(1))

        try:
            pattern = re.compile(match.group(2))
        except re.error as err:
            self.mh.error(obj.location,
                          err.msg)

        for example in examples.value:
            ex_match = pattern.match(example.value)
            if ex_match is None:
                self.mh.error(example.location,
                              "does not match %s" % match.group(2))
            elif ex_match.group(0) != example.value:
                self.mh.error(example.location,
                              "only %s is matched" %
                              (ex_match.group(0)))

        self.token_kinds[match.group(1)] = match.group(2)

    def parse(self, obj):
        assert self.current_lexer is None
        assert isinstance(obj, ast.Record_Object)
        assert obj.e_typ.name == "Grammar"

        # Get original text (without the ''' whitespace
        # simplifications)
        orig_text = obj.field["bnf"].location.text()
        if not orig_text.startswith("'''"):
            self.mh.error(obj.field["bnf"].location,
                          "BNF text must use ''' strings")
        orig_text = orig_text[3:-3]

        # Create nested lexer
        self.current_lexer = BNF_Lexer(self.mh,
                                       orig_text,
                                       obj.field["bnf"].location)
        self.ct = None
        self.nt = self.current_lexer.token()

        self.bundles[obj.name] = []
        while self.nt:
            self.bundles[obj.name].append(self.parse_production())
            self.match("RULE_END")

        self.current_lexer = None
        self.ct            = None
        self.nt            = None

    def parse_production(self):
        # production ::= expansion

        self.match("NONTERMINAL")
        prod_name = self.ct.value[0]
        if prod_name in self.productions:
            self.error(self.ct, "duplicated definition")
        self.match("PRODUCTION")
        self.productions[prod_name] = self.parse_expansion()
        return prod_name

    def parse_expansion(self):
        # expansion ::= string { '|' string }
        #
        # string ::= fragment { fragment }
        #
        # fragment ::= '{' expansion '}'
        #            | '[' expansion ']'
        #            | TERMINAL
        #            | NONTERMINAL
        #            | SYMBOL

        rv = [self.parse_string()]
        while self.peek("ALTERNATIVE"):
            self.match("ALTERNATIVE")
            rv.append(self.parse_string())

        if len(rv) == 1:
            return rv[0]
        else:
            return BNF_Alternatives(rv)

    def parse_string(self):
        rv = [self.parse_fragment()]
        while self.nt.kind in ("C_BRA", "S_BRA",
                               "TERMINAL",
                               "NONTERMINAL",
                               "SYMBOL"):
            rv.append(self.parse_fragment())

        if len(rv) == 1:
            return rv[0]
        else:
            return BNF_String(rv)

    def parse_fragment(self):
        loc = self.nt.location

        if self.peek("C_BRA"):
            self.match("C_BRA")
            rv = self.parse_expansion()
            self.match("C_KET")
            return BNF_Zero_Or_More(loc, rv)

        elif self.peek("S_BRA"):
            self.match("S_BRA")
            rv = self.parse_expansion()
            self.match("S_KET")
            return BNF_Optional(loc, rv)

        elif self.peek("TERMINAL"):
            self.match("TERMINAL")
            return BNF_Literal(loc,
                               self.ct.kind,
                               self.ct.value[0],
                               self.ct.value[1])

        elif self.peek("NONTERMINAL"):
            self.match("NONTERMINAL")
            return BNF_Literal(loc,
                               self.ct.kind,
                               self.ct.value[0],
                               self.ct.value[1])

        elif self.peek("SYMBOL"):
            self.match("SYMBOL")
            return BNF_Literal(loc, self.ct.kind, self.ct.value)

        self.error(self.nt,
                   "expected bnf fragment")


def write_heading(fd, name, depth, anchor=None):
    if anchor:
        fd.write("<h%u id=\"%s\">" % (depth, anchor))
    else:
        fd.write("<h%u>" % depth)
    fd.write(html.escape(name))
    fd.write("</h%u>\n" % depth)


def write_header(fd, obj_version, obj_license):
    ver = obj_version.to_python_dict()
    title = "TRLC Language Reference Manual, Version %u.%u" % (ver["major"],
                                                               ver["minor"])

    fd.write("<!DOCTYPE html>\n")
    fd.write("<html lang=\"en\">\n")
    fd.write("<head>\n")
    fd.write("<title>%s</title>\n" % title)
    fd.write("<meta name=\"viewport\" "
             "content=\"width=device-width, initial-scale=1.0\">\n")
    fd.write("<style>\n")
    fd.write("body {\n")
    fd.write("  font-family: sans;\n")
    fd.write("  margin-left: 1em;\n")
    fd.write("  margin-right: 1em;\n")
    fd.write("}\n")
    fd.write("footer {\n")
    fd.write("  color: %s;\n" % BMW_BLUE_2)
    fd.write("}\n")
    fd.write("h1, h2, h3, h4, h5, h6, h7 {\n")
    fd.write("  color: %s\n" % BMW_BLUE_2)
    fd.write("}\n")
    fd.write("div {\n")
    fd.write("  margin-top: 0.2em;\n")
    fd.write("}\n")
    fd.write("div.code {\n")
    fd.write("  margin-top: 1.5em;\n")
    fd.write("  margin-bottom: 1.5em;\n")
    fd.write("  border-radius: 1em;\n")
    fd.write("  padding: 1em;\n")
    fd.write("  border-left: 0.2em solid %s;\n" % BMW_SILVER)
    fd.write("  border-bottom: 0.2em solid %s;\n" % BMW_SILVER)
    fd.write("}\n")
    fd.write("a {\n")
    fd.write("  color: %s;\n" % BMW_BLUE_1)
    fd.write("}\n")
    fd.write("pre a {\n")
    fd.write("  text-decoration: none;\n")
    fd.write("}\n")
    fd.write("pre a:hover {\n")
    fd.write("  text-decoration: underline;\n")
    fd.write("}\n")
    fd.write("pre i {\n")
    fd.write("  color: %s;\n" % BMW_GREY)
    fd.write("}\n")
    fd.write("span.TRLC_COMMENT {\n")
    fd.write("  font-style: italic;\n")
    fd.write("  color: %s;\n" % BMW_GREY)
    fd.write("}\n")
    fd.write("span.TRLC_KEYWORD {\n")
    fd.write("  font-weight: bold;\n")
    fd.write("  color: %s;\n" % BMW_BLUE_2)
    fd.write("}\n")
    fd.write("span.TRLC_STRING {\n")
    fd.write("  color: %s;\n" % EMACS_STRING)
    fd.write("}\n")
    fd.write(".tooltip {\n")
    fd.write("  position: relative;\n")
    fd.write("  display: inline-block;\n")
    fd.write("}\n")
    fd.write(".tooltip .tooltiptext {\n")
    fd.write("  visibility: hidden;\n")
    fd.write("  background-color: %s;\n" % BMW_SILVER)
    fd.write("  border-radius: 6px;\n")
    fd.write("  padding: 5px;\n")
    fd.write("  position: absolute;\n")
    fd.write("  z-index: 1;\n")
    fd.write("  top: 150%;\n")
    fd.write("  left: 50%;\n")
    fd.write("}\n")
    fd.write(".tooltip:hover .tooltiptext {\n")
    fd.write("  visibility: visible;\n")
    fd.write("}\n")
    fd.write("</style>\n")
    fd.write("</head>\n")
    fd.write("<body>\n")

    write_heading(fd, title, 1)
    lic = obj_license.to_python_dict()
    fd.write("<div>\n")
    fd.write("Permission is granted to copy, distribute and/or"
             " modify this document under the terms of the GNU Free"
             " Documentation License, Version 1.3 or any later version"
             " published by the Free SoftwareFoundation;")
    if not lic["invariant_sections"]:
        fd.write(" with no Invariant Sections,")
    else:
        assert False
    if lic["front_cover"]:
        assert False
    else:
        fd.write(" no Front-Cover Texts,")
    if lic["back_cover"]:
        assert False
    else:
        fd.write(" and no Back-Cover Texts.")
    fd.write("\n")
    fd.write("A copy of the license is included in the section"
             " entitled \"Appendix A: GNU Free Documentation License\".\n")
    fd.write("</div>\n")


def write_footer(fd, script_name):
    write_heading(fd, "Appendix A: GNU Free Documentation License", 1)
    with open("language-reference-manual/LICENSE.html_fragment", "r",
              encoding="UTF-8") as fd_lic:
        fd.write(fd_lic.read())
    fd.write("<hr>\n")
    fd.write("<footer>\n")
    gh_root = "https://github.com/bmw-software-engineering"
    gh_project = "trlc"
    fd.write("Generated by the <a href=\"%s/%s/blob/main/%s\">" %
             (gh_root, gh_project, script_name))
    fd.write("TRLC LRM Generator</a>\n")
    fd.write("</footer>\n")
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


def section_hash(section):
    assert isinstance(section, ast.Section)
    m = hashlib.sha1()
    ptr = section
    while ptr:
        m.update(ptr.name.encode("UTF-8"))
        m.update(b"::")
        ptr = ptr.parent
    return m.hexdigest()


def section_hashes(section):
    assert isinstance(section, ast.Section)
    if section.parent:
        return section_hashes(section.parent) + [section_hash(section)]
    else:
        return [section_hash(section)]


def fmt_text(text):
    text = " ".join(text.replace("\n", " ").split())
    text = html.escape(text)
    text = re.sub(r"`(.*?)`", "<code>\\1</code>", text)
    text = re.sub(r"\*\((.*?)\)\*", "<i>(\\1)</i>", text)
    return text


def write_text_object(fd, mh, obj, context, bnf_parser):
    assert isinstance(mh, Message_Handler)
    assert isinstance(obj, ast.Record_Object)

    data = obj.to_python_dict()

    # Close merged grammar section
    if context["in_grammar"] and (obj.e_typ.name != "Grammar" or
                                  data["text"] or
                                  data["bullets"]):
        context["in_grammar"] = False
        fd.write("</pre>\n")
        fd.write("</div>\n")

    # Build current section
    if obj.section:
        new_section = section_list(obj.section)
        new_hashes  = section_hashes(obj.section)
    else:
        new_section = []

    if obj.e_typ.name in ("Text", "Grammar",
                          "Terminal",
                          "Keywords",
                          "Punctuation"):
        pass
    elif obj.e_typ.name == "Semantics":
        new_section.append(data["kind"] + " Semantics")
    elif obj.e_typ.name == "Name_Resolution":
        new_section.append("Name resolution")
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
            if context["in_grammar"]:
                context["in_grammar"] = False
                fd.write("</pre>\n")
                fd.write("</div>\n")
            if idx < len(new_hashes):
                anchor = "sec:%s" % new_hashes[idx]
            else:
                anchor = None
            write_heading(fd, heading, idx + 2, anchor)

    # Store new section
    context["old_section"] = new_section

    # Emit
    if data["text"] or data["bullets"]:
        fd.write("<div>\n")
        if data["text"]:
            fd.write(fmt_text(data["text"]) + "\n")
        if data["bullets"]:
            fd.write("<ul>\n")
            for item in data["bullets"]:
                fd.write("  <li>%s</li>\n" % fmt_text(item))
            fd.write("</ul>\n")
        fd.write("</div>\n")

    if obj.e_typ.name == "Grammar":
        if context["in_grammar"]:
            fd.write("\n")
        else:
            context["in_grammar"] = True
            fd.write("<div class='code'>\n")
            fd.write("<pre>\n")

    # Emit additional data with semantics
    if obj.e_typ.name == "Terminal":
        match = re.match("([A-Z_]+) *::= *(.*)", data["def"])
        fd.write("<div class='code'>\n")
        fd.write("<code id=\"bnf-%s\">%s</code>\n" %
                 (match.group(1),
                  html.escape(data["def"])))
        fd.write("</div>\n")
        fd.write("<div>\n")
        fd.write("Examples:")
        fd.write("<ul>\n")
        for item in data["examples"]:
            fd.write("  <li>%s</li>\n" % html.escape(item))
        fd.write("</ul>\n")
        fd.write("</div>\n")

    elif obj.e_typ.name == "Grammar":
        first = True
        for production in bnf_parser.bundles[obj.name]:
            if first:
                first = False
            else:
                fd.write("\n")
            write_production(fd, production, bnf_parser)

    elif obj.e_typ.name == "Example":
        fd.write("<div class='code'>\n")
        fd.write("<pre>\n")
        write_example(fd, mh, obj)
        fd.write("</pre>\n")
        fd.write("</div>\n")


class Nested_Lexer(TRLC_Lexer):
    def __init__(self, string_literal):
        assert isinstance(string_literal, ast.String_Literal)
        mh = string_literal.location.lexer.mh
        if not string_literal.location.text().startswith("'''"):
            mh.error(string_literal.location,
                     "only ''' strings are supported for examples")
        super().__init__(
            mh           = mh,
            file_name    = string_literal.location.lexer.file_name,
            file_content = string_literal.location.text()[3:-3])
        self.base = string_literal.location

    def token(self):
        tok = super().token()
        if tok:
            sref = Source_Reference(
                lexer      = self.base.lexer,
                start_line = self.base.line_no + (tok.location.line_no - 1),
                start_col  = (self.base.col_no + 3
                              if tok.location.line_no == 1
                              else tok.location.col_no),
                start_pos  = self.base.start_pos + 3 + tok.location.start_pos,
                end_pos    = self.base.start_pos + 3 + tok.location.end_pos)
            tok.location = sref
        return tok


class Token_Buffer(TRLC_Lexer):
    def __init__(self, lexer):
        assert isinstance(lexer, TRLC_Lexer)
        super().__init__(mh        = lexer.mh,
                         file_name = lexer.file_name)
        self.lexer  = lexer
        self.tokens = []

    def token(self):
        tok = self.lexer.token()
        if tok:
            self.tokens.append(tok)
        return tok

    def as_html(self):
        if not self.tokens:
            return ""

        rv = ""

        min_col = min(tok.location.col_no for tok in self.tokens)

        cl = self.tokens[0].location.line_no
        cc = min_col
        for tok in self.tokens:
            if tok.location.line_no != cl:
                rv += "\n" * (tok.location.line_no - cl)
                cc = min_col
                cl = tok.location.line_no
            spaces = tok.location.col_no - cc
            rv += " " * spaces
            cc += spaces
            rv += "<span class=\"TRLC_%s\">" % tok.kind
            rv += html.escape(tok.location.text())
            rv += "</span>"
            cc += len(tok.location.text())

        return rv


class Chained_Lexer(TRLC_Lexer):
    def __init__(self, literals):
        assert isinstance(literals, list) and len(literals) >= 1
        for literal in literals:
            assert isinstance(literal, ast.String_Literal)
        self.lexers  = list(map(Token_Buffer, map(Nested_Lexer, literals)))
        self.current = self.lexers[0]
        self.future  = self.lexers[1:]
        super().__init__(literals[0].location.lexer.mh,
                         literals[0].location.file_name)

    def token(self):
        while self.current:
            tok = self.current.token()
            if tok:
                return tok
            elif self.future:
                self.current = self.future[0]
                self.future  = self.future[1:]
            else:
                self.current = None
        return None


def write_example(fd, mh, obj):
    assert isinstance(obj, ast.Record_Object)
    assert obj.e_typ.name == "Example"

    stab = ast.Symbol_Table.create_global_table(mh)

    # Parse virtual RSL file
    rsl_sources = []
    if isinstance(obj.field["hidden_rsl"], ast.String_Literal):
        rsl_sources.append(obj.field["hidden_rsl"])
    if isinstance(obj.field["rsl"], ast.String_Literal):
        rsl_sources.append(obj.field["rsl"])
    rsl_lexers = Chained_Lexer(rsl_sources)
    rsl_parser = Parser(mh        = mh,
                        stab      = stab,
                        file_name = obj.location.file_name,
                        lint_mode = False,
                        lexer     = rsl_lexers)
    rsl_parser.parse_rsl_header()
    rsl_parser.parse_rsl_file()

    # Parse virtual TRLC file
    trlc_sources = []
    if isinstance(obj.field["hidden_trlc"], ast.String_Literal):
        trlc_sources.append(obj.field["hidden_trlc"])
    if isinstance(obj.field["trlc"], ast.String_Literal):
        trlc_sources.append(obj.field["trlc"])
    if trlc_sources:
        trlc_lexers = Chained_Lexer(trlc_sources)
        trlc_parser = Parser(mh        = mh,
                             stab      = stab,
                             file_name = obj.location.file_name,
                             lint_mode = False,
                             lexer     = trlc_lexers)
        trlc_parser.parse_trlc_file()
    else:
        trlc_parser = None

    data = obj.to_python_dict()
    if data["rsl"]:
        fd.write(rsl_lexers.lexers[-1].as_html())
    else:
        fd.write(trlc_lexers.lexers[-1].as_html())


def write_production(fd, production, bnf_parser):
    # Write indicator with anchor
    fd.write("<span id=\"bnf-%s\">%s</span> ::= " %
             (production, production))
    n_exp = bnf_parser.productions[production]
    alt_offset = len(production) + 3

    if isinstance(n_exp, BNF_Alternatives):
        write_expansion(fd, n_exp.members[0], bnf_parser)
        fd.write("\n")
        for n_member in n_exp.members[1:]:
            fd.write(" " * alt_offset + "| ")
            write_expansion(fd, n_member, bnf_parser)
            fd.write("\n")

    elif isinstance(n_exp, BNF_String):
        write_expansion(fd, n_exp.members[0], bnf_parser)
        current_line = n_exp.members[0].location.line_no
        for n_member in n_exp.members[1:]:
            if n_member.location.line_no == current_line:
                fd.write(" ")
            else:
                current_line = n_member.location.line_no
                fd.write("\n" + " " * (alt_offset + 2))
            write_expansion(fd, n_member, bnf_parser)
        fd.write("\n")

    else:
        write_expansion(fd, n_exp, bnf_parser)
        fd.write("\n")


def write_expansion(fd, n_exp, bnf_parser):
    if isinstance(n_exp, BNF_Alternatives):
        first = True
        for n_member in n_exp.members:
            if first:
                first = False
            else:
                fd.write(" | ")
            write_expansion(fd, n_member, bnf_parser)

    elif isinstance(n_exp, BNF_String):
        first = True
        for n_member in n_exp.members:
            if first:
                first = False
            else:
                fd.write(" ")
            write_expansion(fd, n_member, bnf_parser)

    elif isinstance(n_exp, BNF_Optional):
        fd.write("[ ")
        write_expansion(fd, n_exp.expansion, bnf_parser)
        fd.write(" ]")

    elif isinstance(n_exp, BNF_Zero_Or_More):
        fd.write("{ ")
        write_expansion(fd, n_exp.expansion, bnf_parser)
        fd.write(" }")

    else:
        assert isinstance(n_exp, BNF_Literal)

        if n_exp.kind == "SYMBOL":
            fd.write("'")
            fd.write(html.escape(n_exp.value))
            fd.write("'")

        elif n_exp.kind == "TERMINAL":
            if n_exp.value in bnf_parser.token_kinds:
                fd.write("<span class=\"tooltip\">")
                fd.write("<a href=\"#bnf-%s\">" % html.escape(n_exp.value))
            fd.write(n_exp.value)
            if n_exp.value in bnf_parser.token_kinds:
                fd.write("</a>")
                fd.write("<span class=\"tooltiptext\">%s</span>" %
                         html.escape(bnf_parser.token_kinds[n_exp.value]))
                fd.write("</span>")
            if n_exp.name:
                fd.write("<i>_%s</i>" % n_exp.name)

        else:
            assert n_exp.kind == "NONTERMINAL"
            if n_exp.value in bnf_parser.productions:
                tooltip_text = str(bnf_parser.productions[n_exp.value])
                if len(tooltip_text) > 50:
                    tooltip_text = None
            else:
                tooltip_text = None
            if tooltip_text:
                fd.write("<span class=\"tooltip\">")
            if n_exp.value in bnf_parser.productions:
                fd.write("<a href=\"#bnf-%s\">" % html.escape(n_exp.value))
            fd.write(n_exp.value)
            if n_exp.value in bnf_parser.productions:
                fd.write("</a>")
            if tooltip_text:
                fd.write("<span class=\"tooltiptext\">%s</span>" %
                         html.escape(tooltip_text))
                fd.write("</span>")
            if n_exp.name:
                fd.write("<i>_%s</i>" % n_exp.name)


def write_toc_section(fd, tree, level):
    if len(tree) == 0:
        return

    indent = " " * (4 * (level - 1))
    fd.write(indent + "<ol>\n")
    for item in tree.values():
        fd.write(indent + "  <li><a href=\"#sec:%s\">%s</a>\n" %
                 (section_hash(item["obj"]),
                  item["name"]))
        write_toc_section(fd, item["sub"], level + 1)
        fd.write(indent + "  </li>\n")
    fd.write(indent + "</ol>\n")


def write_toc(fd, pkg_lrm):
    tree = OrderedDict()

    old_section = None
    for obj in pkg_lrm.symbols.iter_record_objects():
        if not obj.section:
            continue
        if old_section == obj.section:
            continue
        old_section = obj.section

        sections = []
        ptr = obj.section
        while ptr:
            sections = [ptr] + sections
            ptr = ptr.parent

        ptr = tree
        for section in sections:
            if section.name not in ptr:
                ptr[section.name] = {
                    "name" : section.name,
                    "obj"  : section,
                    "sub"  : OrderedDict()
                }
            ptr = ptr[section.name]["sub"]

    write_toc_section(fd, tree, 1)


def main():
    mh = Message_Handler()
    sm = Source_Manager(mh)

    sm.register_directory("language-reference-manual")
    symbols = sm.process()
    if symbols is None:
        sys.exit(1)

    pkg_lrm = symbols.lookup_assuming(mh, "LRM", ast.Package)
    obj_license = pkg_lrm.symbols.lookup_assuming(mh,
                                                  "License",
                                                  ast.Record_Object)
    obj_version = pkg_lrm.symbols.lookup_assuming(mh,
                                                  "Version",
                                                  ast.Record_Object)
    typ_text = pkg_lrm.symbols.lookup_assuming(mh, "Text", ast.Record_Type)
    typ_gram = pkg_lrm.symbols.lookup_assuming(mh, "Grammar", ast.Record_Type)
    typ_kword = pkg_lrm.symbols.lookup_assuming(mh, "Keywords",
                                                ast.Record_Type)
    typ_punct = pkg_lrm.symbols.lookup_assuming(mh, "Punctuation",
                                                ast.Record_Type)
    typ_terminal = pkg_lrm.symbols.lookup_assuming(mh, "Terminal",
                                                   ast.Record_Type)

    # Process grammer
    parser = BNF_Parser(mh)
    for obj in pkg_lrm.symbols.iter_record_objects():
        if obj.e_typ.is_subclass_of(typ_gram):
            try:
                parser.parse(obj)
            except TRLC_Error:
                return
        elif obj.e_typ.is_subclass_of(typ_kword):
            for kwobj in obj.field["bullets"].value:
                try:
                    parser.register_terminal(kwobj)
                except TRLC_Error:
                    return
        elif obj.e_typ.is_subclass_of(typ_punct):
            for kwobj in obj.field["bullets"].value:
                try:
                    parser.register_backtick_terminals(kwobj)
                except TRLC_Error:
                    return
        elif obj.e_typ.is_subclass_of(typ_terminal):
            try:
                parser.register_token(obj.field["def"], obj.field["examples"])
            except TRLC_Error:
                return
    try:
        parser.sem()
    except TRLC_Error:
        return

    context = {
        "old_section" : None,
        "in_grammar"  : False
    }
    with open("docs/lrm.html", "w", encoding="UTF-8") as fd:
        write_header(fd, obj_version, obj_license)
        write_toc(fd, pkg_lrm)
        for obj in pkg_lrm.symbols.iter_record_objects():
            if obj.e_typ.is_subclass_of(typ_text):
                try:
                    write_text_object(fd, mh, obj, context, parser)
                except TRLC_Error:
                    return
        if context["in_grammar"]:
            context["in_grammar"] = False
            fd.write("</pre>\n")
            fd.write("</div>\n")

        write_footer(fd, os.path.relpath(__file__))


if __name__ == "__main__":
    main()
