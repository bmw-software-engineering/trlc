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

import sys
import enum

from trlc import version


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
        rv = self.file_name
        if self.line_no:
            rv += ":%u" % self.line_no
            if self.col_no and include_column:
                rv += ":%u" % self.col_no
        return rv

    def context_lines(self):
        return []

    def get_end_location(self):
        """Get location point to the end of this location

        When we generate a location for a longer sequence then this
        function gets the "end" of it::

           for example here
               ^^^^^^^ this is the whole range
               ^ file/line/col points here
                     ^ file/line/col of end_location points here

        :returns: a pointer to the last character in a location
        :rtype: Location

        """
        return self


@enum.unique
class Kind(enum.Enum):
    SYS_ERROR = enum.auto()
    SYS_CHECK = enum.auto()
    SYS_WARNING = enum.auto()
    USER_ERROR = enum.auto()
    USER_WARNING = enum.auto()

    def __str__(self):
        return {"SYS_ERROR"    : "error",
                "SYS_CHECK"    : "issue",
                "SYS_WARNING"  : "warning",
                "USER_ERROR"   : "check error",
                "USER_WARNING" : "check warning"}[self.name]


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
        assert isinstance(kind, Kind)
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

    :attribute errors: Number of system or user errors raised
    :type: int

    :attribute supressed: Number of messages supressed by policy
    :type: int

    """
    def __init__(self, brief=False, detailed_info=True):
        assert isinstance(brief, bool)
        self.brief         = brief
        self.show_details  = detailed_info
        self.warnings      = 0
        self.errors        = 0
        self.suppressed    = 0
        self.sm            = None
        self.suppress_kind = set()

    def suppress(self, kind):
        assert isinstance(kind, Kind)
        self.suppress_kind.add(kind)

    def cross_file_reference(self, location):
        assert isinstance(location, Location)

        if self.sm is None:
            return location.to_string(include_column=False)
        else:
            return self.sm.cross_file_reference(location)

    def emit(self,
             location,
             kind,
             message,
             fatal=True,
             extrainfo=None,
             category=None):
        assert isinstance(location, Location)
        assert isinstance(kind, Kind)
        assert isinstance(message, str)
        assert isinstance(fatal, bool)
        assert isinstance(extrainfo, str) or extrainfo is None
        assert isinstance(category, str) or category is None

        if self.brief:
            context = None
            msg = "%s: trlc %s: %s" % (location.to_string(),
                                       str(kind),
                                       message)

        else:
            context = location.context_lines()
            msg = "%s: %s: %s" % (location.to_string(len(context) == 0),
                                  str(kind),
                                  message)

        if category:
            msg += " [%s]" % category

        if kind in self.suppress_kind:
            self.suppressed += 1

        else:
            if context:
                assert len(context) == 2
                print(context[0].replace("\t", " "))
                print(context[1].replace("\t", " "), msg)
            else:
                print(msg)

            if not self.brief \
               and self.show_details \
               and extrainfo:
                if context:
                    indent = len(context[1]) - 1
                else:
                    indent = 0
                for line in extrainfo.splitlines():
                    print("%s| %s" % (" " * indent,
                                      line.rstrip()))

        if fatal:
            raise TRLC_Error(location, kind, message)

    def lex_error(self, location, message):
        assert isinstance(location, Location)
        assert isinstance(message, str)

        self.errors += 1
        self.emit(location = location,
                  kind     = Kind.SYS_ERROR,
                  message  = message)

    def error(self,
              location,
              message,
              explanation=None,
              fatal=True,
              user=False):
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
        assert isinstance(explanation, str) or explanation is None
        assert isinstance(fatal, bool)
        assert isinstance(user, bool)

        if user:
            kind = Kind.USER_ERROR
        else:
            kind = Kind.SYS_ERROR

        self.errors += 1
        self.emit(location  = location,
                  kind      = kind,
                  message   = message,
                  fatal     = fatal,
                  extrainfo = explanation)

    def warning(self, location, message, explanation=None, user=False):
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
        assert isinstance(explanation, str) or explanation is None
        assert isinstance(user, bool)

        if user:
            kind = Kind.USER_WARNING
        else:
            kind = Kind.SYS_WARNING

        self.warnings += 1
        self.emit(location  = location,
                  kind      = kind,
                  message   = message,
                  extrainfo = explanation,
                  fatal     = False)

    def check(self, location, message, check, explanation=None):
        assert isinstance(location, Location)
        assert isinstance(message, str)
        assert isinstance(check, str)
        assert isinstance(explanation, str) or explanation is None

        self.warnings += 1
        self.emit(location  = location,
                  kind      = Kind.SYS_CHECK,
                  message   = message,
                  fatal     = False,
                  extrainfo = explanation,
                  category  = check)

    def ice_loc(self, location, message):  # pragma: no cover
        assert isinstance(location, Location)
        assert isinstance(message, str)

        self.errors += 1
        self.emit(location  = location,
                  kind      = Kind.SYS_ERROR,
                  message   = message,
                  extrainfo = "please report this to %s" % version.BUGS_URL,
                  fatal     = False)
        sys.exit(1)
