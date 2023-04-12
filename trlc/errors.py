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

import os.path
import sys


class Location:
    """Reference to a source or virtual location

    Any message raised by the :class:`Message_Handler` will be
    attached to a given location. This location can be real
    (i.e. something in a file) or virtual (i.e. a builtin function).

    :attribute file_name: the name of the file or virtual location
    :type: str

    :attribute line_no: an optional line number, starting at 1
    :type: int

    :attribute col_no: an optional column number, starting at 1
    :type: int:
    """
    def __init__(self, file_name, line_no=None, col_no=None):
        assert isinstance(file_name, str)
        if line_no is not None:
            assert isinstance(line_no, int)
            assert line_no >= 1
        if col_no is not None:
            assert isinstance(col_no, int)
            assert col_no >= 1
        self.file_name   = file_name
        self.line_no     = line_no
        self.col_no      = col_no

    def to_string(self, include_column=True):
        """Return a nice string representation

        The style is the gcc-style file:line:column format. Note that
        the filename is stripped of its path in order to make the
        final message smaller.

        :param include_column: If set, include the column location (if \
        there is one)
        :type include_column: bool

        :returns: a formatted location
        :rtype: str

        """
        rv = os.path.relpath(self.file_name)
        if self.line_no:
            rv += ":%u" % self.line_no
            if self.col_no and include_column:
                rv += ":%u" % self.col_no
        return rv

    def context_lines(self):
        return []


class TRLC_Error(Exception):
    """ The universal exception that TRLC raises if something goes wrong

    :attribute location: Where the issue originates from
    :type: Location

    :attribute kind: The kind of problem (e.g. lex error, error, warning, etc.)
    :type: str

    :attribute message: Description of the problem
    :type: str
    """
    def __init__(self, location, kind, message):
        assert isinstance(location, Location)
        assert isinstance(kind, str)
        assert isinstance(message, str)

        super().__init__()
        self.location = location
        self.kind     = kind
        self.message  = message


class Message_Handler:
    """Universal message handler

    All messages from TRLC are processed by this class. If you want to
    write a tool that emits additional messages then it would be a
    really good idea to also use this class. Do not use your own print
    statements.

    If the location comes from the location attribute of
    :class:`~trlc.ast.Node` then you also get context provided for
    free.

    :attribute brief: When true displays as much context as possible
    :type: Boolean

    :attribute warnings: Number of system or user warnings raised
    :type: int

    :attribute error: Number of system or user errors raised
    :type: int

    """
    def __init__(self, brief=False):
        assert isinstance(brief, bool)
        self.brief    = brief
        self.warnings = 0
        self.errors   = 0
        self.sm       = None

    def cross_file_reference(self, location):
        assert isinstance(location, Location)

        if self.sm is None:
            return location.to_string(include_column=False)
        else:
            return self.sm.cross_file_reference(location)

    def emit(self, location, kind, message, fatal=True):
        assert isinstance(location, Location)
        assert isinstance(kind, str)
        assert isinstance(message, str)
        assert isinstance(fatal, bool)

        if self.brief:
            context = None
            msg = "%s: trlc %s: %s" % (location.to_string(),
                                       kind,
                                       message)

        else:
            context = location.context_lines()
            msg = "%s: %s: %s" % (location.to_string(len(context) == 0),
                                  kind,
                                  message)

        if context:
            assert len(context) == 2
            print(context[0].replace("\t", " "))
            print(context[1].replace("\t", " "), msg)
        else:
            print(msg)

        if fatal:
            raise TRLC_Error(location, kind, message)

    def lex_error(self, location, message):
        assert isinstance(location, Location)
        assert isinstance(message, str)

        self.errors += 1
        self.emit(location, "lex error", message)

    def error(self, location, message, fatal=True, user=False):
        """ Create an error message

        For example::

           mh.error(my_expr.location, "potato")

        Might generate this output::

           x = 5 + 2
                 ^ foo.check:5: error: potato

        :param location: where to attach the message
        :type location: Location

        :param message: the message to print
        :type message: str

        :param fatal: should we raise an exception in addition to printing \
        the error?
        :type fatal: bool

        :param user: if set print "check error:" instead of "error:"
        :type user: bool

        :raises TRLC_Error: if fatal is true
        """

        assert isinstance(location, Location)
        assert isinstance(message, str)

        if user:
            kind = "check error"
        else:
            kind = "error"

        self.errors += 1
        self.emit(location, kind, message, fatal)

    def warning(self, location, message, user=False):
        """ Create a warning message

        :param location: where to attach the message
        :type location: Location
        :param message: the message to print
        :type message: str
        :param user: if set print "check warning:" instead of "warning:"
        :type user: bool
        """
        assert isinstance(location, Location)
        assert isinstance(message, str)

        if user:
            kind = "check warning"
        else:
            kind = "warning"

        self.warnings += 1
        self.emit(location, kind, message, fatal=False)

    def ice_loc(self, location, message):  # pragma: no cover
        assert isinstance(location, Location)
        assert isinstance(message, str)

        self.errors += 1
        self.emit(location, "ICE", message, fatal=False)
        sys.exit(1)
