#!/usr/bin/env python3
#
# TRLC - Treat Requirements Like Code
# Copyright (C) 2022-2023 Bayerische Motoren Werke Aktiengesellschaft (BMW AG)
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
import argparse
import subprocess
from fractions import Fraction

from trlc import ast
from trlc import lint
from trlc.errors import TRLC_Error, Location, Message_Handler, Kind
from trlc.parser import Parser
from trlc.lexer import TRLC_Lexer
from trlc.version import TRLC_VERSION, BUGS_URL

# pylint: disable=unused-import
try:
    import cvc5
    VCG_API_AVAILABLE = True
except ImportError:
    VCG_API_AVAILABLE = False


class Source_Manager:
    """Dependency and source manager for TRLC.

    This is the main entry point when using the Python API. Create an
    instance of this, register the files you want to look at, and
    finally call the process method.

    :param mh: The message handler to use
    :type mh: Message_Handler

    :param error_recovery: If true attempts to continue parsing after \
      errors. This may generate weird error messages since it's impossible \
      to reliably recover the parse context in all cases.
    :type error_recovery: bool

    :param lint_mode: If true enables additional warning messages.
    :type lint_mode: bool

    :param verify_mode: If true performs in-depth static analysis for \
      user-defined checks. Requires CVC5 and PyVCG to be installed.
    :type verify_mode: bool

    :param parse_trlc: If true parses trlc files, otherwise they are \
      ignored.
    :type parse_trlc: bool

    :param debug_vcg: If true and verify_mode is also true, emit the \
      individual SMTLIB2 VCs and generate a picture of the program \
      graph. Requires Graphviz to be installed.
    :type parse_trlc: bool

    """
    def __init__(self, mh,
                 lint_mode      = True,
                 parse_trlc     = True,
                 verify_mode    = False,
                 debug_vcg      = False,
                 error_recovery = True,
                 cvc5_binary    = None):
        assert isinstance(mh, Message_Handler)
        assert isinstance(lint_mode, bool)
        assert isinstance(parse_trlc, bool)
        assert isinstance(verify_mode, bool)
        assert isinstance(debug_vcg, bool)
        assert isinstance(cvc5_binary, str) or cvc5_binary is None

        self.mh          = mh
        self.mh.sm       = self
        self.stab        = ast.Symbol_Table.create_global_table(mh)
        self.rsl_files   = {}
        self.check_files = {}
        self.trlc_files  = {}
        self.packages    = {}

        self.lint_mode      = lint_mode
        self.parse_trlc     = parse_trlc
        self.verify_mode    = verify_mode
        self.debug_vcg      = debug_vcg
        self.error_recovery = error_recovery
        self.cvc5_binary    = cvc5_binary

        self.exclude_patterns = []
        self.common_root      = None

        self.progress_current = 0
        self.progress_final   = 0

    def callback_parse_begin(self):
        pass

    def callback_parse_progress(self, progress):
        assert isinstance(progress, int)

    def callback_parse_end(self):
        pass

    def signal_progress(self):
        self.progress_current += 1
        if self.progress_final:
            progress = (self.progress_current * 100) // self.progress_final
        else:
            progress = 100
        self.callback_parse_progress(min(progress, 100))

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

    def create_parser(self, file_name, file_content=None):
        assert os.path.isfile(file_name)
        assert isinstance(file_content, str) or file_content is None

        lexer = TRLC_Lexer(self.mh, file_name, file_content)

        return Parser(mh             = self.mh,
                      stab           = self.stab,
                      file_name      = file_name,
                      lint_mode      = self.lint_mode,
                      error_recovery = self.error_recovery,
                      lexer          = lexer)

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

    def register_file(self, file_name, file_content=None):
        """Schedule a file for parsing.

        :param file_name: name of the file
        :type file_name: str
        :raise AssertionError: if the file does not exist
        :raise AssertionError: if the file is registed more than once
        :raise TRLC_Error: if the file is not a rsl/check/trlc file

        :param file_content: content of the file
        :type file_content: str
        :raise AssertionError: if the content is not of type string

        :return: true if the file could be registered without issues
        :rtype: bool
        """
        assert os.path.isfile(file_name)
        assert isinstance(file_content, str) or file_content is None
        # lobster-trace: LRM.Layout

        ok = True
        try:
            if file_name.endswith(".rsl"):
                self.register_rsl_file(file_name, file_content)
            elif file_name.endswith(".check"):
                self.register_check_file(file_name, file_content)
            elif file_name.endswith(".trlc"):
                self.register_trlc_file(file_name, file_content)
            else:
                ok = False
                self.mh.error(Location(os.path.basename(file_name)),
                              "is not a rsl, check, or trlc file",
                              fatal = False)
        except TRLC_Error:
            ok = False

        if ok:
            self.progress_final += 1

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
        # lobster-trace: LRM.Layout

        ok = True
        for path, dirs, files in os.walk(dir_name):
            dirs.sort()

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

    def register_rsl_file(self, file_name, file_content=None):
        assert os.path.isfile(file_name)
        assert file_name not in self.rsl_files
        assert isinstance(file_content, str) or file_content is None
        # lobster-trace: LRM.Preamble

        self.update_common_root(file_name)

        self.rsl_files[file_name] = self.create_parser(file_name, file_content)
        self.rsl_files[file_name].parse_preamble("rsl")

        self.register_package(
            package_name = self.rsl_files[file_name].cu.package.name,
            file_name    = file_name)
        for import_name in self.rsl_files[file_name].cu.raw_imports:
            self.register_dependency(
                package_name = self.rsl_files[file_name].cu.package.name,
                import_name  = import_name.value)

    def register_check_file(self, file_name, file_content=None):
        assert os.path.isfile(file_name)
        assert file_name not in self.check_files
        assert isinstance(file_content, str) or file_content is None

        self.update_common_root(file_name)
        self.check_files[file_name] = self.create_parser(file_name,
                                                         file_content)

    def register_trlc_file(self, file_name, file_content=None):
        assert os.path.isfile(file_name)
        assert file_name not in self.trlc_files
        assert isinstance(file_content, str) or file_content is None

        if not self.parse_trlc:
            return

        self.update_common_root(file_name)
        self.trlc_files[file_name] = self.create_parser(file_name,
                                                        file_content)

    def parse_rsl_files(self):
        # lobster-trace: LRM.Preamble

        ok = True

        # First, check that each package import is known
        for parser in self.rsl_files.values():
            parser.cu.resolve_imports(self.mh, self.stab)

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
                # lobster-trace: LRM.Circular_Dependencies
                conflicts = list(sorted(self.packages))
                if self.mh.brief:
                    self.mh.error(
                        Location(list(self.packages.values())[0]["file"]),
                        "circular inheritence between %s" %
                        " | ".join(conflicts),
                        fatal = False)
                    return False
                else:
                    for name in conflicts:
                        deps = sorted(set(self.packages[name]["deps"]) -
                                      processed_packages)
                        print("> %s depends on %s" %
                              (name,
                               ", ".join(deps)))
                    self.mh.error(
                        Location(list(self.packages.values())[0]["file"]),
                        "circular inheritence",
                        fatal = False)
                    return False

            for pkg in sorted(work_list):
                try:
                    parser  = self.rsl_files[self.packages[pkg]["file"]]
                    ok     &= parser.parse_rsl_file()
                    self.signal_progress()
                except TRLC_Error:
                    ok = False
                processed_packages.add(pkg)
                del self.packages[pkg]

        return ok

    def parse_check_files(self):
        # lobster-trace: LRM.Preamble

        ok = True
        for name in sorted(self.check_files):
            try:
                ok &= self.check_files[name].parse_check_file()
                self.signal_progress()
            except TRLC_Error:
                ok = False
        return ok

    def parse_trlc_files(self):
        # lobster-trace: LRM.Preamble

        ok = True

        # First, pre-parse the file_preamble of all files to discover
        # all late packages
        packages_with_errors = set()
        for name in sorted(self.trlc_files):
            try:
                self.trlc_files[name].parse_preamble("trlc")
            except TRLC_Error:
                packages_with_errors.add(name)
                ok = False

        # Then actually parse
        for name in sorted(self.trlc_files):
            if name in packages_with_errors:
                continue
            try:
                ok &= self.trlc_files[name].parse_trlc_file()
                self.signal_progress()
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
        linter = lint.Linter(mh            = self.mh,
                             stab          = self.stab,
                             verify_checks = self.verify_mode,
                             debug_vcg     = self.debug_vcg,
                             cvc5_binary   = self.cvc5_binary)
        return linter.verify()

    def process(self):
        """Parse all registered files.

        :return: a symbol table (or None if there were any errors)
        :rtype: Symbol_Table
        """
        # lobster-trace: LRM.File_Parsing_Order

        # Notify callback
        self.callback_parse_begin()
        self.progress_current = 0

        # Parse RSL files (topologically sorted, in order to deal with
        # dependencies)
        ok = self.parse_rsl_files()

        if not self.error_recovery and not ok:
            self.callback_parse_end()
            return None

        # Parse check files. At this point we cannot introduce anything
        # new in terms of packages.
        ok &= self.parse_check_files()

        if not self.error_recovery and not ok:
            self.callback_parse_end()
            return None

        # Perform sanity checks (enabled by default). We only do this
        # if there were no errors so far.
        if self.lint_mode and ok:
            ok &= self.perform_sanity_checks()

        # Stop here if we're not processing TRLC files.
        if not self.parse_trlc:
            self.callback_parse_end()
            if ok:
                return self.stab
            else:
                return None

        # Parse TRLC files. Almost all the semantic analysis and name
        # resolution happens here, with the notable exception of resolving
        # record references (as we can have circularity here).
        if not self.parse_trlc_files():
            self.callback_parse_end()
            return None

        # Resolve record reference names and do the missing semantic
        # analysis.
        # lobster-trace: LRM.File_Parsing_References
        if not self.resolve_record_references():
            self.callback_parse_end()
            return None

        if not ok:
            self.callback_parse_end()
            return None

        # Finally, apply user defined checks
        if not self.perform_checks():
            self.callback_parse_end()
            return None

        self.callback_parse_end()
        return self.stab


def main():
    ap = argparse.ArgumentParser(
        prog="trlc",
        description="TRLC %s (Python reference implementation)" % TRLC_VERSION,
        epilog=("TRLC is licensed under the GPLv3."
                " Report bugs here: %s" % BUGS_URL),
        allow_abbrev=False,
    )
    og_lint = ap.add_argument_group("analysis options")
    og_lint.add_argument("--no-lint",
                         default=False,
                         action="store_true",
                         help="Disable additional, optional warnings.")
    og_lint.add_argument("--skip-trlc-files",
                         default=False,
                         action="store_true",
                         help=("Only process model and check files,"
                               " do not process trlc files."))
    og_lint.add_argument("--verify",
                         default=False,
                         action="store_true",
                         help=("[EXPERIMENTAL] Attempt to statically"
                               " verify absence of errors in user defined"
                               " checks. Does not yet support all language"
                               " constructs. Requires PyVCG to be "
                               " installed."))
    og_lint.add_argument("--use-cvc5-binary",
                         default=None,
                         help=("[EXPERIMENTAL] Drive the given CVC5 solver"
                               " with SMTLIB2 input instead of using the"
                               " API."))

    og_input = ap.add_argument_group("input options")
    og_input.add_argument("--include-bazel-dirs",
                          action="store_true",
                          help=("Enter bazel-* directories, which are"
                                " excluded by default."))

    og_output = ap.add_argument_group("output options")
    og_output.add_argument("--brief",
                           default=False,
                           action="store_true",
                           help=("Simpler output intended for CI. Does not"
                                 " show context or additional information."))
    og_output.add_argument("--no-detailed-info",
                           default=False,
                           action="store_true",
                           help=("Do not print counter-examples and other"
                                 " supplemental information on failed"
                                 " checks. The specific values of"
                                 " counter-examples are unpredictable"
                                 " from system to system, so if you need 100%"
                                 " reproducible output then use this option."))
    og_output.add_argument("--no-user-warnings",
                           default=False,
                           action="store_true",
                           help=("Do not display any warnings from user"
                                 " defined checks, only errors."))
    og_output.add_argument("--no-error-recovery",
                           default=False,
                           action="store_true",
                           help=("By default the tool attempts to recover"
                                 " from parse errors to show more errors, but"
                                 " this can occasionally generate weird"
                                 " errors. You can use this option to stop"
                                 " at the first real errors."))
    og_output.add_argument("--show-file-list",
                           action="store_true",
                           help=("If there are no errors, produce a summary"
                                 " naming every file processed."))
    og_output.add_argument("--error-on-warnings",
                           action="store_true",
                           help=("If there are warnings, return status code"
                                 " 1 instead of 0."))

    og_debug = ap.add_argument_group("debug options")
    og_debug.add_argument("--debug-dump",
                          default=False,
                          action="store_true",
                          help="Dump symbol table.")
    og_debug.add_argument("--debug-api-dump",
                          default=False,
                          action="store_true",
                          help=("Dump json of to_python_object() for all"
                                " objects."))
    og_debug.add_argument("--debug-vcg",
                          default=False,
                          action="store_true",
                          help=("Emit graph and individual VCs. Requires"
                                " graphviz to be installed."))

    ap.add_argument("items",
                    nargs="*",
                    metavar="DIR|FILE")
    options = ap.parse_args()

    if options.verify and not (options.use_cvc5_binary or
                               VCG_API_AVAILABLE):
        ap.error("The --verify option requires the optional dependency"
                 " CVC5 or use of the --use-cvc5-binary option")

    if options.use_cvc5_binary:
        if not options.verify:
            ap.error("The --use-cvc5-binary requires the --verify option")
        try:
            result = subprocess.run([options.use_cvc5_binary,
                                     "--version"],
                                    check          = True,
                                    capture_output = True,
                                    encoding       = "UTF-8")
            if not result.stdout.startswith("This is cvc5"):
                ap.error("selected binary does not appear to be CVC5")
        except OSError as err:
            ap.error("cannot run %s: %s" % (options.use_cvc5_binary,
                                            str(err)))
        except subprocess.CalledProcessError:
            ap.error("cannot run %s" % options.use_cvc5_binary)

    mh = Message_Handler(options.brief, not options.no_detailed_info)

    if options.no_user_warnings:
        mh.suppress(Kind.USER_WARNING)

    sm = Source_Manager(mh             = mh,
                        lint_mode      = not options.no_lint,
                        parse_trlc     = not options.skip_trlc_files,
                        verify_mode    = options.verify,
                        debug_vcg      = options.debug_vcg,
                        error_recovery = not options.no_error_recovery,
                        cvc5_binary    = options.use_cvc5_binary)

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

    if not options.brief:
        summary = "Processed %u model(s)" % len(sm.rsl_files)
        if options.skip_trlc_files:
            summary += " and"
        else:
            summary += ","
        summary += " %u check(s)" % len(sm.check_files)
        if not options.skip_trlc_files:
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

        if mh.suppressed:
            summary += " with %u supressed messages" % mh.suppressed

        print(summary)

    if options.show_file_list and ok:
        for filename in sorted(sm.rsl_files):
            print("> Model %s (Package %s)" %
                  (filename, sm.rsl_files[filename].cu.package.name))
        for filename in sorted(sm.check_files):
            print("> Checks %s (Package %s)" %
                  (filename, sm.check_files[filename].cu.package.name))
        if not options.skip_trlc_files:
            for filename in sorted(sm.trlc_files):
                print("> Requirements %s (Package %s)" %
                      (filename, sm.trlc_files[filename].cu.package.name))

    if ok:
        if options.error_on_warnings and mh.warnings:
            return 1
        else:
            return 0
    else:
        return 1


if __name__ == "__main__":
    sys.exit(main())
