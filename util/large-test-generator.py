#!/usr/bin/env python3

import os
import argparse
import random
from pprint import pprint

STRING_CONTENT_SINGLE = "".join(chr(c)
                                for c in range(0x200)
                                if (chr(c).isprintable() and
                                    chr(c) != "\n"))
STRING_CONTENT_TRIPLE = "".join(chr(c)
                                for c in range(0x200)
                                if chr(c).isprintable())

def generate_string(options):
    if random.randint(0, 1):
        delim = '"'
        content = STRING_CONTENT_SINGLE
        escape = '"'
        banned = "\\"
    else:
        delim = "'''"
        content = STRING_CONTENT_TRIPLE
        escape = None
        banned = "'"

    string = "".join(random.choice(content)
                     for _ in range(random.randint(25, 200)))

    if banned is not None:
        string = string.replace(banned, "")

    if escape is not None:
        string = string.replace(escape, "\\" + escape)

    return delim + string + delim


def generate_tests(options):
    random.seed(42)


    packages = ["generic"]
    for i in range(options.packages - 1):
        packages.append("package_%u" % (i + 1))

    with open("generic.rsl", "w") as fd:
        fd.write("package generic\n\n")
        fd.write("type Requirement {\n")
        fd.write("  description optional String\n")
        fd.write("  links optional Requirement [1 .. *]\n")
        fd.write("}\n")

    tree = {pkg: set() for pkg in packages}
    for pkg_id, pkg in enumerate(packages[1:], 1):
        tree[pkg].add("generic")
        tree[pkg] |= set(random.choices(
            packages[1:pkg_id] + packages[pkg_id + 1:],
            k = random.randint(0, options.max_imports_per_package)))

    # packages -> files -> items
    items = {}
    pkg_items = {"generic" : []}
    for pkg_name in packages[1:]:
        items[pkg_name] = {}
        pkg_items[pkg_name] = []
        num_files = random.randint(1, options.max_files_per_package)
        num_items = random.randint(options.max_items_per_package // 3,
                                   options.max_items_per_package)
        offset = 1
        for file_id in range(1, num_files + 1):
            file_name = "%s_%u.trlc" % (pkg_name,
                                        file_id)
            if file_id == num_files:
                item_count = num_items
            else:
                item_count = random.randint(0, num_items * 2 // 3)
                num_items -= item_count

            items[pkg_name][file_name] = ["Item_%u" % (offset + item_id)
                                          for item_id in range(item_count)]
            pkg_items[pkg_name] += items[pkg_name][file_name]
            offset += item_count

    total_pkg = 1
    total_items = 0
    for pkg_name in packages[1:]:
        total_pkg += 1
        with open(pkg_name + ".rsl", "w") as fd:
            fd.write("package %s\n\n" % pkg_name)
        for file_name in items[pkg_name]:
            with open(file_name, "w") as fd:
                fd.write("package %s\n" % pkg_name)
                for import_name in tree[pkg_name]:
                    fd.write("import %s\n" % import_name)
                fd.write("\n")

                for item_name in items[pkg_name][file_name]:
                    total_items += 1
                    links = random.choices(
                        pkg_items[pkg_name] +
                        ["%s.%s" % (p_name, i_name)
                         for p_name in tree[pkg_name]
                         for i_name in pkg_items[p_name]],
                        k = random.randint(0, options.max_links_per_item))
                    fd.write("generic.Requirement %s {\n" % item_name)
                    fd.write("  description = %s\n" % generate_string(options))
                    if links:
                        fd.write("  links = [%s]\n" % ", ".join(links))
                    fd.write("}\n\n")

    print("Wrote %u items over %u packages." % (total_items,
                                                total_pkg))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("target",
                    help="generate test in this directory")
    ap.add_argument("--packages",
                    type=int,
                    default=100)
    ap.add_argument("--max-files-per-package",
                    type=int,
                    default=10)
    ap.add_argument("--max-items-per-package",
                    type=int,
                    default=1500)
    ap.add_argument("--max-imports-per-package",
                    type=int,
                    default=2)
    ap.add_argument("--max-links-per-item",
                    type=int,
                    default=5)

    options = ap.parse_args()

    if os.path.isdir(options.target):
        pass
    elif not os.path.exists(options.target):
        os.mkdir(options.target)
    else:
        ap.error("%s exists and is not a directory" % options.target)

    os.chdir(options.target)
    generate_tests(options)


if __name__ == "__main__":
    main()
