#!/usr/bin/env python3

"""
This little hack draws a hierarchy of the AST nodes in GraphViz format.
"""

import inspect
import argparse

import trlc.ast

DOC_BASE = "https://bmw-software-engineering.github.io/trlc/manual/ast.html"

def main():
    ap = argparse.ArgumentParser()
    options = ap.parse_args()

    module = trlc.ast
    root   = module.Node

    print("digraph {")
    print('rankdir="LR";')
    for name, c in inspect.getmembers(module, inspect.isclass):
        if not issubclass(c, root):
            continue
        url = "%s#trlc.ast.%s" % (DOC_BASE,
                                  name)
        doc = c.__doc__.split("\n\n", 1)[0]
        print('"%s" [href="%s", shape=none, fontcolor="#0969da", tooltip="%s"];' % (name, url, doc))
        for b in c.__bases__:
            if issubclass(b, root):
                print('"%s" -> "%s";' % (b.__name__, name))
    print("}")


if __name__ == "__main__":
    main()
