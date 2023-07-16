#!/usr/bin/env python3

"""
This little hack draws a hierarchy of the parser and lexer nodes
in GraphViz format.
"""

import inspect
import argparse
import numbers

import trlc.ast
import trlc.lexer
import trlc.parser
import trlc.nested
import trlc.errors

DOC_BASE = "https://github.com/bmw-software-engineering/trlc/blob/main/trlc/"

def is_ignored(cls):
    if cls is object:
        return True
    elif issubclass(cls, (trlc.ast.Node,
                          trlc.errors.Message_Handler,
                          numbers.Rational,
                          type)):
        return True
    else:
        return False


def main():
    ap = argparse.ArgumentParser()
    options = ap.parse_args()

    actioned = set()

    print('digraph "Lexer/Parser Hierarchy" {')
    print('rankdir="LR";')
    for module in (trlc.lexer, trlc.parser, trlc.nested):
        doc_base = DOC_BASE + module.__name__.replace("trlc.", "") + ".py"
        for name, c in inspect.getmembers(module, inspect.isclass):
            if is_ignored(c) or c in actioned:
                continue
            actioned.add(c)
            url = "%s#L%u" % (doc_base, inspect.getsourcelines(c)[1])
            if c.__doc__ is None:
                doc = ""
            else:
                doc = c.__doc__.split("\n\n", 1)[0]
            print('"%s" [href="%s", shape=none, fontcolor="#0969da", tooltip="%s"];' % (name, url, doc))
            for b in c.__bases__:
                if is_ignored(b):
                    continue
                print('"%s" -> "%s";' % (b.__name__, name))
    print("}")


if __name__ == "__main__":
    main()
