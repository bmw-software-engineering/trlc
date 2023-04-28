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

import re
import os
import sys
import json
from argparse import ArgumentParser
from fractions import Fraction

from trlc import ast
from trlc import lint
from trlc.errors import TRLC_Error, Location, Message_Handler
from trlc.parser import Parser
from trlc.version import TRLC_VERSION


class Source_Manager:
    """Dependency and source manager for TRLC.

    This is the main entry point when using the Python API. Create an
    instance of this, register the files you want to look at, and
    finally call the process method.

    :param mh: The message handler to use
    :type mh: Message_Handler

    :param lint_mode: If true check rules and models. If false actually \
    process objects.
    :type mh: Message_Handler

    """
    def __init__(self, mh, lint_mode=False):
        assert isinstance(mh, Message_Handler)
        assert isinstance(lint_mode, bool)

        self.mh          = mh
        self.mh.sm       = self
        self.stab        = ast.Symbol_Table.create_global_table(mh)
        self.rsl_files   = {}
        self.check_files = {}
        self.trlc_files  = {}
        self.packages    = {}
        self.lint_mode   = lint_mode

        self.exclude_patterns = []

        self.common_root    = None

    def cross_file_reference(self, location):
        assert isinstance(location, Location)

        if self.common_root is None:
            return location.to_string(False)
        else:
            return "%s:%u" % (os.path.relpath(location.file_name,
                                              self.common_root),
                              location.line_no)

    def update_common_root(self, file_name):
        assert isinstance(file_name, str)

        if self.common_root is None:
            self.common_root = os.path.dirname(os.path.abspath(file_name))
        else:
            new_root = os.path.dirname(os.path.abspath(file_name))
            for n, (char_a, char_b) in enumerate(zip(self.common_root,
                                                     new_root)):
                if char_a != char_b:
                    self.common_root = self.common_root[0:n]
                    break

    def create_parser(self, file_name):
        assert os.path.isfile(file_name)

        return Parser(mh           = self.mh,
                      stab         = self.stab,
                      file_name    = file_name,
                      lint_mode    = self.lint_mode)

    def register_package(self, package_name, file_name=None):
        if package_name in self.packages:
            self.packages[package_name]["file"] = file_name
        else:
            self.packages[package_name] = {"name" : package_name,
                                           "deps" : set(),
                                           "file" : file_name}

    def register_dependency(self, package_name, import_name):
        if import_name not in self.packages:
            self.register_package(import_name)
        self.packages[package_name]["deps"].add(import_name)

    def register_file(self, file_name):
        """Schedule a file for parsing.

        :param file_name: name of the file
        :type file_name: str
        :raise AssertionError: if the file does not exist
        :raise AssertionError: if the file is registed more than once
        :raise TRLC_Error: if the file is not a rsl/check/trlc file

        :return: true if the file could be registered without issues
        :rtype: bool
        """
        assert os.path.isfile(file_name)

        ok = True
        if file_name.endswith(".rsl"):
            try:
                self.register_rsl_file(file_name)
            except TRLC_Error:
                ok = False
        elif file_name.endswith(".check"):
            self.register_check_file(file_name)
        elif file_name.endswith(".trlc"):
            self.register_trlc_file(file_name)
        else:
            ok = False
            self.mh.error(Location(os.path.basename(file_name)),
                          "is not a rsl, check, or trlc file")

        return ok

    def register_directory(self, dir_name):
        """Schedule a directory tree for parsing.

        :param dir_name: name of the directory
        :type file_name: str
        :raise AssertionError: if the directory does not exist
        :raise AssertionError: if any item in the directory is already \
        registered
        :raise TRLC_Error: on any parse errors

        :return: true if the directory could be registered without issues
        :rtype: bool
        """
        assert os.path.isdir(dir_name)

        ok = True
        for path, dirs, files in os.walk(dir_name):
            for n, dirname in reversed(list(enumerate(dirs))):
                keep = True
                for exclude_pattern in self.exclude_patterns:
                    if exclude_pattern.match(dirname):
                        keep = False
                        break
                if not keep:
                    del dirs[n]

            for file_name in sorted(files):
                if os.path.splitext(file_name)[1] in (".rsl",
                                                      ".check",
                                                      ".trlc"):
                    ok &= self.register_file(os.path.join(path, file_name))
        return ok

    def register_rsl_file(self, file_name):
        assert os.path.isfile(file_name)
        assert file_name not in self.rsl_files

        self.update_common_root(file_name)

        self.rsl_files[file_name] = self.create_parser(file_name)
        self.rsl_files[file_name].parse_rsl_header()

        self.register_package(
            package_name = self.rsl_files[file_name].pkg.name,
            file_name    = file_name)
        for import_name in self.rsl_files[file_name].raw_deps:
            self.register_dependency(
                package_name = self.rsl_files[file_name].pkg.name,
                import_name  = import_name.value)

    def register_check_file(self, file_name):
        assert os.path.isfile(file_name)
        assert file_name not in self.check_files

        self.update_common_root(file_name)
        self.check_files[file_name] = self.create_parser(file_name)

    def register_trlc_file(self, file_name):
        assert os.path.isfile(file_name)
        assert file_name not in self.trlc_files

        self.update_common_root(file_name)
        self.trlc_files[file_name] = self.create_parser(file_name)

    def parse_rsl_files(self):
        # First, check that each package import is known
        for parser in self.rsl_files.values():
            for t_import in parser.raw_deps:
                parser.deps.append(parser.stab.lookup(self.mh,
                                                      t_import,
                                                      ast.Package))

        # Second, parse packages that have no unparsed
        # dependencies. Keep doing it until we parse everything or
        # until we have reached a fix point (in which case we have a
        # cycle in our dependencies).
        processed_packages = set()
        while self.packages:
            work_list = [pkg_name
                         for pkg_name, pkg in self.packages.items()
                         if pkg_name not in processed_packages and
                            pkg["deps"] <= processed_packages]

            if not work_list:
                conflicts = list(sorted(self.packages))
                if self.mh.brief:
                    self.mh.error(
                        Location(list(self.packages.values())[0]["file"]),
                        "circular inheritence between %s" %
                        " | ".join(conflicts))
                else:
                    for name in conflicts:
                        deps = sorted(set(self.packages[name]["deps"]) -
                                      processed_packages)
                        print("> %s depends on %s" %
                              (name,
                               ", ".join(deps)))
                    self.mh.error(
                        Location(list(self.packages.values())[0]["file"]),
                        "circular inheritence")

            for pkg in sorted(work_list):
                self.rsl_files[self.packages[pkg]["file"]].parse_rsl_file()
                processed_packages.add(pkg)
                del self.packages[pkg]

    def parse_check_files(self):
        ok = True
        for name in sorted(self.check_files):
            try:
                self.check_files[name].parse_check_file()
            except TRLC_Error:
                ok = False
        return ok

    def parse_trlc_files(self):
        ok = True
        for name in sorted(self.trlc_files):
            try:
                self.trlc_files[name].parse_trlc_file()
            except TRLC_Error:
                ok = False
        return ok

    def resolve_record_references(self):
        ok = True
        for package in self.stab.values(ast.Package):
            for obj in package.symbols.values(ast.Record_Object):
                try:
                    obj.resolve_references(self.mh)
                except TRLC_Error:
                    ok = False

        return ok

    def perform_checks(self):
        ok = True
        for package in self.stab.values(ast.Package):
            for obj in package.symbols.values(ast.Record_Object):
                try:
                    if not obj.perform_checks(self.mh):
                        ok = False
                except TRLC_Error:
                    ok = False

        return ok

    def perform_sanity_checks(self):
        linter = lint.Linter(self.mh, self.stab)
        return linter.verify()

    def process(self):
        """Parse all registered files.

        :return: a symbol table (or None if there were any errors)
        :rtype: Symbol_Table
        """
        # Parse RSL files (topologically sorted, in order to deal with
        # dependencies)
        try:
            self.parse_rsl_files()
        except TRLC_Error:
            return None

        # Parse check files. At this point we cannot introduce anything
        # new in terms of packages.
        ok = True
        if not self.parse_check_files():
            ok = False

        # If we run in lint mode, then we perform the checks now and then
        # stop. We do not process the TRLC files.
        if self.lint_mode:
            if not ok:
                return None
            self.perform_sanity_checks()
            return None if self.mh.errors or self.mh.warnings else self.stab

        # Parse TRLC files. Almost all the semantic analysis and name
        # resolution happens here, with the notable exception of resolving
        # record references (as we can have circularity here).
        if not self.parse_trlc_files():
            return None

        # Resolve record reference names and do the missing semantic
        # analysis.
        if not self.resolve_record_references():
            return None

        if not ok:
            return None

        # Finally, apply user defined checks
        if not self.perform_checks():
            return None

        return self.stab


def main():
    ap = ArgumentParser(
        description="TRLC %s (Python reference implementation)" % TRLC_VERSION
    )
    op_mode = ap.add_mutually_exclusive_group()
    op_mode.add_argument("--lint",
                         default=False,
                         action="store_true",
                         help="sanity check models and checks")
    ap.add_argument("--debug-dump",
                    default=False,
                    action="store_true",
                    help="dump symbol table")
    ap.add_argument("--debug-api-dump",
                    default=False,
                    action="store_true",
                    help="dump json")
    ap.add_argument("--brief",
                    default=False,
                    action="store_true",
                    help="simpler output intended for CI")
    ap.add_argument("items",
                    nargs="*",
                    metavar="DIR|FILE")
    ap.add_argument("--include-bazel-dirs",
                    action="store_true",
                    help="by default we do not enter bazel-* directories")
    ap.add_argument("--show-file-list",
                    action="store_true",
                    help=("if there are no errors, produce a summary "
                          "naming every file processed"))
    options = ap.parse_args()

    mh = Message_Handler(options.brief)
    sm = Source_Manager(mh, options.lint)

    if not options.include_bazel_dirs:
        sm.exclude_patterns.append(re.compile("^bazel-.*$"))

    for path_name in options.items:
        if not (os.path.isdir(path_name) or
                os.path.isfile(path_name)):
            ap.error("%s is not a file or directory" % path_name)

    # Process input files, defaulting to the current directory if none
    # given.
    ok = True
    if options.items:
        for path_name in options.items:
            if os.path.isdir(path_name):
                ok &= sm.register_directory(path_name)
            else:
                try:
                    ok &= sm.register_file(path_name)
                except TRLC_Error:
                    ok = False
    else:
        ok &= sm.register_directory(".")

    if not ok:
        return 1

    if sm.process() is None:
        ok = False

    if ok:
        if options.debug_dump:
            sm.stab.dump()
        if options.debug_api_dump:
            tmp = {}
            for obj in sm.stab.iter_record_objects():
                tmp[obj.name] = obj.to_python_dict()
                for key in tmp[obj.name]:
                    if isinstance(tmp[obj.name][key], Fraction):
                        tmp[obj.name][key] = float(tmp[obj.name][key])

            print(json.dumps(tmp, indent=2, sort_keys=True))

    if options.show_file_list or options.lint:
        if options.lint:
            summary = "Verified"
        else:
            summary = "Processed"

        summary += " %u model(s)" % len(sm.rsl_files)
        if options.lint:
            summary += " and"
        else:
            summary += ", "
        summary += " %u check(s)" % len(sm.check_files)
        if not options.lint:
            summary += " and %u requirement file(s)" % len(sm.trlc_files)

        summary += " and found"

        if mh.errors and mh.warnings:
            summary += " %u warning(s)" % mh.warnings
            summary += " and %u error(s)" % mh.errors
        elif mh.warnings:
            summary += " %u warning(s)" % mh.warnings
        elif mh.errors:
            summary += " %u error(s)" % mh.errors
        else:
            summary += " no issues"

        print(summary)

        if options.show_file_list and ok:
            for filename in sorted(sm.rsl_files):
                print("> Model %s (Package %s)" %
                      (filename, sm.rsl_files[filename].pkg.name))
            for filename in sorted(sm.check_files):
                print("> Checks %s (Package %s)" %
                      (filename, sm.check_files[filename].pkg.name))
            if not options.lint:
                for filename in sorted(sm.trlc_files):
                    print("> Requirements %s (Package %s)" %
                          (filename, sm.trlc_files[filename].pkg.name))

    if ok:
        return 0
    else:
        return 1


if __name__ == "__main__":
    sys.exit(main())
