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

import argparse
import json
import os
import re
import subprocess
import sys
from fractions import Fraction

from trlc import ast, lint
from trlc.errors import Kind, Location, Message_Handler, TRLC_Error
from trlc.lexer import Token_Stream
from trlc.parser import Parser
from trlc.version import BUGS_URL, TRLC_VERSION

# pylint: disable=unused-import
try:
    import cvc5
    VCG_API_AVAILABLE = True
except ImportError:  # pragma: no cover
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
        self.includes    = {}
        self.rsl_files   = {}
        self.trlc_files  = {}
        self.all_files   = {}
        self.dep_graph   = {}

        self.files_with_preamble_errors = set()

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
        else:  # pragma: no cover
            progress = 100
        self.callback_parse_progress(min(progress, 100))

    def cross_file_reference(self, location):
        assert isinstance(location, Location)

        if self.common_root is None:
            return location.to_string(False)
        elif location.line_no is None:
            return os.path.relpath(location.file_name,
                                   self.common_root)
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

    def create_parser(self, file_name, file_content=None, primary_file=True):
        assert os.path.isfile(file_name)
        assert isinstance(file_content, str) or file_content is None
        assert isinstance(primary_file, bool)

        lexer = Token_Stream(self.mh, file_name, file_content)

        return Parser(mh             = self.mh,
                      stab           = self.stab,
                      file_name      = file_name,
                      lint_mode      = self.lint_mode,
                      error_recovery = self.error_recovery,
                      primary_file   = primary_file,
                      lexer          = lexer)

    def register_include(self, dir_name):
        """Make contents of a directory available for automatic inclusion

        :param dir_name: name of the directory
        :type dir_name: str
        :raise AssertionError: if dir_name is not a directory
        """
        assert os.path.isdir(dir_name)

        for path, dirs, files in os.walk(dir_name):
            for n, dirname in reversed(list(enumerate(dirs))):
                keep = True
                for exclude_pattern in self.exclude_patterns:
                    if exclude_pattern.match(dirname):
                        keep = False
                        break
                if not keep:
                    del dirs[n]

            self.includes.update(
                {os.path.abspath(full_name): full_name
                 for full_name in
                   (os.path.join(path, file_name)
                    for file_name in files
                    if os.path.splitext(file_name)[1] in (".rsl",
                                                          ".trlc"))})

    def register_file(self, file_name, file_content=None, primary=True):
        """Schedule a file for parsing.

        :param file_name: name of the file
        :type file_name: str
        :raise AssertionError: if the file does not exist
        :raise AssertionError: if the file is registed more than once
        :raise TRLC_Error: if the file is not a rsl/trlc file

        :param file_content: content of the file
        :type file_content: str
        :raise AssertionError: if the content is not of type string

        :param primary: should be False if the file is a potential \
          include file, and True otherwise.
        :type primary: bool

        :return: true if the file could be registered without issues
        :rtype: bool
        """
        assert os.path.isfile(file_name)
        assert isinstance(file_content, str) or file_content is None
        # lobster-trace: LRM.Layout

        ok = True
        try:
            if file_name.endswith(".rsl"):
                self.register_rsl_file(file_name, file_content, primary)
            elif file_name.endswith(".trlc"):
                self.register_trlc_file(file_name, file_content, primary)
            else:  # pragma: no cover
                ok = False
                self.mh.error(Location(os.path.basename(file_name)),
                              "is not a rsl or trlc file",
                              fatal = False)
        except TRLC_Error:
            ok = False

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
                                                      ".trlc"):
                    ok &= self.register_file(os.path.join(path, file_name))
        return ok

    def register_rsl_file(self, file_name, file_content=None, primary=True):
        assert os.path.isfile(file_name)
        assert file_name not in self.rsl_files
        assert isinstance(file_content, str) or file_content is None
        assert isinstance(primary, bool)
        # lobster-trace: LRM.Preamble

        self.update_common_root(file_name)
        parser = self.create_parser(file_name,
                                    file_content,
                                    primary)
        self.rsl_files[file_name] = parser
        self.all_files[file_name] = parser
        if os.path.abspath(file_name) in self.includes:
            del self.includes[os.path.abspath(file_name)]

    def register_trlc_file(self, file_name, file_content=None, primary=True):
        # lobster-trace: LRM.TRLC_File
        assert os.path.isfile(file_name)
        assert file_name not in self.trlc_files
        assert isinstance(file_content, str) or file_content is None
        assert isinstance(primary, bool)
        # lobster-trace: LRM.Preamble

        if not self.parse_trlc:  # pragma: no cover
            # Not executed as process should exit before we attempt this.
            return

        self.update_common_root(file_name)
        parser = self.create_parser(file_name,
                                    file_content,
                                    primary)
        self.trlc_files[file_name] = parser
        self.all_files[file_name] = parser
        if os.path.abspath(file_name) in self.includes:
            del self.includes[os.path.abspath(file_name)]

    def build_graph(self):
        # lobster-trace: LRM.Preamble

        # Register all include files not yet registered
        for file_name in list(sorted(self.includes.values())):
            self.register_file(file_name, primary=False)

        # Parse preambles and build dependency graph
        ok = True
        graph = self.dep_graph
        files = {}
        for container, kind in ((self.rsl_files, "rsl"),
                                (self.trlc_files, "trlc")):
            # First parse preamble and register packages in graph
            for file_name in sorted(container):
                try:
                    parser = container[file_name]
                    parser.parse_preamble(kind)
                    pkg_name = parser.cu.package.name
                    if (pkg_name , "rsl") not in graph:
                        graph[(pkg_name , "rsl")] = set()
                        graph[(pkg_name , "trlc")] = set([(pkg_name , "rsl")])
                        files[(pkg_name , "rsl")] = set()
                        files[(pkg_name , "trlc")] = set()
                    files[(pkg_name , kind)].add(file_name)
                except TRLC_Error:
                    ok = False
                    self.files_with_preamble_errors.add(file_name)

            # Then parse all imports and add all valid links
            for file_name in sorted(container):
                if file_name in self.files_with_preamble_errors:
                    continue

                parser = container[file_name]
                if parser.cu.package is None:
                    continue
                pkg_name = parser.cu.package.name
                parser.cu.resolve_imports(self.mh, self.stab)

                graph[(pkg_name , kind)] |= \
                    {(imported_pkg.name , kind)
                     for imported_pkg in parser.cu.imports}

        # Build closure for our files
        work_list = {(parser.cu.package.name , "rsl")
                     for parser in self.rsl_files.values()
                     if parser.cu.package and parser.primary}
        work_list |= {(parser.cu.package.name , "trlc")
                      for parser in self.trlc_files.values()
                      if parser.cu.package and parser.primary}
        work_list &= set(graph)

        required = set()
        while work_list:
            node = work_list.pop()
            required.add(node)
            work_list |= (graph[node] - required) & set(graph)

        # Expand into actual file list and flag dependencies
        file_list = {file_name
                     for node in required
                     for file_name in files[node]}
        for file_name in file_list:
            if not self.all_files[file_name].primary:
                self.all_files[file_name].secondary = True

        # Record total files that need parsing
        self.progress_final = len(file_list)

        return ok

    def parse_rsl_files(self):
        # lobster-trace: LRM.Preamble
        # lobster-trace: LRM.RSL_File

        ok = True

        # Select RSL files that we should parse
        rsl_map = {(parser.cu.package.name , "rsl"): parser
                   for parser in self.rsl_files.values()
                   if parser.cu.package and (parser.primary or
                                             parser.secondary)}

        # Parse packages that have no unparsed dependencies. Keep
        # doing it until we parse everything or until we have reached
        # a fix point (in which case we have a cycle in our
        # dependencies).
        work_list = set(rsl_map)
        processed = set()
        while work_list:
            candidates = {node
                          for node in work_list
                          if len(self.dep_graph.get(node, set()) -
                                 processed) == 0}
            if not candidates:
                # lobster-trace: LRM.Circular_Dependencies
                sorted_work_list = sorted(work_list)
                offender = rsl_map[sorted_work_list[0]]
                names = {rsl_map[node].cu.package.name:
                         rsl_map[node].cu.location
                         for node in sorted_work_list[1:]}
                self.mh.error(
                    location    = offender.cu.location,
                    message     = ("circular inheritence between %s" %
                                   " | ".join(sorted(names))),
                    explanation = "\n".join(
                        sorted("%s is declared in %s" %
                               (name,
                                self.mh.cross_file_reference(loc))
                               for name, loc in names.items())),
                    fatal       = False)
                return False

            for node in sorted(candidates):
                try:
                    ok &= rsl_map[node].parse_rsl_file()
                    self.signal_progress()
                except TRLC_Error:
                    ok = False
                processed.add(node)

            work_list -= candidates

        return ok

    def parse_trlc_files(self):
        # lobster-trace: LRM.TRLC_File
        # lobster-trace: LRM.Preamble

        ok = True

        # Then actually parse
        for name in sorted(self.trlc_files):
            parser = self.trlc_files[name]
            if name in self.files_with_preamble_errors:
                continue
            if not (parser.primary or parser.secondary):
                continue

            try:
                ok &= parser.parse_trlc_file()
                self.signal_progress()
            except TRLC_Error:
                ok = False

        return ok

    def resolve_record_references(self):
        # lobster-trace: LRM.Markup_String_Late_Reference_Resolution
        # lobster-trace: LRM.Late_Reference_Checking
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

    def process(self):
        """Parse all registered files.

        :return: a symbol table (or None if there were any errors)
        :rtype: Symbol_Table
        """
        # lobster-trace: LRM.File_Parsing_Order

        # Notify callback
        self.callback_parse_begin()
        self.progress_current = 0

        # Build dependency graph
        ok = self.build_graph()

        # Parse RSL files (topologically sorted, in order to deal with
        # dependencies)
        ok &= self.parse_rsl_files()

        if not self.error_recovery and not ok:  # pragma: no cover
            self.callback_parse_end()
            return None

        # Perform sanity checks (enabled by default). We only do this
        # if there were no errors so far.
        if self.lint_mode and ok:
            linter = lint.Linter(mh            = self.mh,
                                 stab          = self.stab,
                                 verify_checks = self.verify_mode,
                                 debug_vcg     = self.debug_vcg,
                                 cvc5_binary   = self.cvc5_binary)
            ok &= linter.perform_sanity_checks()
        # Stop here if we're not processing TRLC files.
        if not self.parse_trlc:  # pragma: no cover
            self.callback_parse_end()
            if ok:
                return self.stab
            else:
                return None

        # Parse TRLC files. Almost all the semantic analysis and name
        # resolution happens here, with the notable exception of resolving
        # record references (as we can have circularity here).
        if not self.parse_trlc_files():  # pragma: no cover
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

        if self.lint_mode and ok:
            linter.verify_imports()

        self.callback_parse_end()
        return self.stab


def trlc():
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
                         help=("Only process rsl files,"
                               " do not process any trlc files."))
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
    og_input.add_argument("-I",
                          action="append",
                          dest="include_dirs",
                          help=("Add include path. Files from these"
                                " directories are parsed only when needed."
                                " Can be specified more than once."),
                          default=[])

    og_output = ap.add_argument_group("output options")
    og_output.add_argument("--version",
                           default=False,
                           action="store_true",
                           help="Print TRLC version and exit.")
    og_output.add_argument("--brief",
                           default=False,
                           action="store_true",
                           help=("Simpler output intended for CI. Does not"
                                 " show context or additional information,"
                                 " but prints the usual summary at the end."))
    og_output.add_argument("--no-detailed-info",
                           default=False,
                           action="store_true",
                           help=("Do not print counter-examples and other"
                                 " supplemental information on failed"
                                 " checks. The specific values of"
                                 " counter-examples are unpredictable"
                                 " from system to system, so if you need"
                                 " perfectly reproducible output then use"
                                 " this option."))
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

    if options.version:  # pragma: no cover
        print(TRLC_VERSION)
        sys.exit(0)

    if options.verify and not (options.use_cvc5_binary or
                               VCG_API_AVAILABLE):  # pragma: no cover
        ap.error("The --verify option requires the optional dependency"
                 " CVC5 or use of the --use-cvc5-binary option")

    if options.use_cvc5_binary:  # pragma: no cover
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

    if options.no_user_warnings:  # pragma: no cover
        mh.suppress(Kind.USER_WARNING)

    sm = Source_Manager(mh             = mh,
                        lint_mode      = not options.no_lint,
                        parse_trlc     = not options.skip_trlc_files,
                        verify_mode    = options.verify,
                        debug_vcg      = options.debug_vcg,
                        error_recovery = not options.no_error_recovery,
                        cvc5_binary    = options.use_cvc5_binary)

    if not options.include_bazel_dirs:  # pragma: no cover
        sm.exclude_patterns.append(re.compile("^bazel-.*$"))

    # Process includes
    ok = True
    for path_name in options.include_dirs:
        if not os.path.isdir(path_name):
            ap.error("include path %s is not a directory" % path_name)
    for path_name in options.include_dirs:
        sm.register_include(path_name)

    # Process input files, defaulting to the current directory if none
    # given.
    for path_name in options.items:
        if not (os.path.isdir(path_name) or
                os.path.isfile(path_name)):  # pragma: no cover
            ap.error("%s is not a file or directory" % path_name)
    if options.items:
        for path_name in options.items:
            if os.path.isdir(path_name):
                ok &= sm.register_directory(path_name)
            else:  # pragma: no cover
                try:
                    ok &= sm.register_file(path_name)
                except TRLC_Error:
                    ok = False
    else:  # pragma: no cover
        ok &= sm.register_directory(".")

    if not ok:
        return 1

    if sm.process() is None:
        ok = False

    if ok:
        if options.debug_dump:  # pragma: no cover
            sm.stab.dump()
        if options.debug_api_dump:
            tmp = {}
            for obj in sm.stab.iter_record_objects():
                tmp[obj.name] = obj.to_python_dict()
                for key in tmp[obj.name]:
                    if isinstance(tmp[obj.name][key], Fraction):
                        tmp[obj.name][key] = float(tmp[obj.name][key])

            print(json.dumps(tmp, indent=2, sort_keys=True))

    total_models = len(sm.rsl_files)
    parsed_models = len([item
                            for item in sm.rsl_files.values()
                            if item.primary or item.secondary])
    total_trlc = len(sm.trlc_files)
    parsed_trlc = len([item
                        for item in sm.trlc_files.values()
                        if item.primary or item.secondary])

    def count(parsed, total, what):
        rv = str(parsed)
        if parsed < total:
            rv += " (of %u)" % total
        rv += " " + what
        if total == 0 or total > 1:
            rv += "s"
        return rv

    summary = "Processed %s" % count(parsed_models,
                                        total_models,
                                        "model")

    if not options.skip_trlc_files:  # pragma: no cover
        summary += " and %s" % count(parsed_trlc,
                                        total_trlc,
                                        "requirement file")

    summary += " and found"

    if mh.errors and mh.warnings:
        summary += " %s" % count(mh.warnings, mh.warnings, "warning")
        summary += " and %s" % count(mh.errors, mh.errors, "error")
    elif mh.warnings:
        summary += " %s" % count(mh.warnings, mh.warnings, "warning")
    elif mh.errors:
        summary += " %s" % count(mh.errors, mh.errors, "error")
    else:
        summary += " no issues"

    if mh.suppressed:  # pragma: no cover
        summary += " with %u supressed messages" % mh.suppressed

    print(summary)

    if options.show_file_list and ok:  # pragma: no cover
        def get_status(parser):
            if parser.primary:
                return "[Primary] "
            elif parser.secondary:
                return "[Included]"
            else:
                return "[Excluded]"

        for filename in sorted(sm.rsl_files):
            parser = sm.rsl_files[filename]
            print("> %s Model %s (Package %s)" %
                  (get_status(parser),
                   filename,
                   parser.cu.package.name))
        if not options.skip_trlc_files:
            for filename in sorted(sm.trlc_files):
                parser = sm.trlc_files[filename]
                print("> %s Requirements %s (Package %s)" %
                      (get_status(parser),
                       filename,
                       parser.cu.package.name))

    if ok:
        if options.error_on_warnings and mh.warnings \
           or mh.errors:  # pragma: no cover
            return 1
        return 0
    return 1


def main():
    try:
        return trlc()
    except BrokenPipeError:
        # Python flushes standard streams on exit; redirect remaining output
        # to devnull to avoid another BrokenPipeError at shutdown
        devnull = os.open(os.devnull, os.O_WRONLY)
        os.dup2(devnull, sys.stdout.fileno())
        return 141


if __name__ == "__main__":
    sys.exit(main())
