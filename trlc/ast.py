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

from copy import copy
from difflib import get_close_matches
from enum import Enum, auto
from collections import OrderedDict

from trlc.errors import Location, Message_Handler
from trlc.lexer import Token
from trlc import math

#
# This module defines the AST and related object for the TRLC
# reference implementation. There are four sections:
#
# - Valuations deal with concrete values for record objects
# - AST expressions deal with the syntax tree
# - AST entities deal with concrete objects that have been declared
# - Symbol_Table and scope deals with name resolution
#


##############################################################################
# Valuations
##############################################################################

class Value:
    """Polymorphic value for evaluating expressions.

    Any record references will be fully resolved.

    :attribute location: source location this value comes from
    :type: Location

    :attribute value: the value or None (for null values)
    :type: str, int, bool, list[Value], Record_Reference, \
    Enumeration_Literal_Spec

    :attribute typ: type of the value (or None for null values)
    :type: Type
    """
    def __init__(self, location, value, typ):
        assert isinstance(location, Location)
        assert value is None or \
            isinstance(value, (str,
                               int,
                               bool,
                               list,
                               Record_Reference,
                               Enumeration_Literal_Spec))
        assert typ is None or isinstance(typ, Type)
        assert (typ is None) == (value is None)

        self.location = location
        self.value    = value
        self.typ      = typ

    def __repr__(self):  # pragma: no cover
        return "Value(%s)" % self.value

    def resolve_references(self, mh):
        assert isinstance(mh, Message_Handler)

        if isinstance(self.value, Record_Reference):
            self.value.resolve(mh)


##############################################################################
# AST Nodes
##############################################################################

class Node:
    """Base class for all AST items.

    :attribute location: source location
    :type: Location
    """
    def __init__(self, location):
        assert isinstance(location, Location)
        self.location = location

    def write_indent(self, indent, message):  # pragma: no cover
        assert isinstance(indent, int)
        assert indent >= 0
        assert isinstance(message, str)
        print(" " * (3 * indent) + message)

    def dump(self, indent=0):  # pragma: no cover
        """Visualise the parse tree.

        This can be called for any :class:`Node` or
        :class:`Symbol_Table`, and can be very helpful for debugging
        or understanding the parse tree. The dump methods will produce
        output like this::

            Symbol_Table
               Builtin_Boolean
               Builtin_Integer
               Builtin_String
               Package bar
                  Symbol_Table
                     Record_Type MyType
                        Record_Component name
                           Optional: False
                           Type: String
                        Checks
                           Error 'description is too short'
                              Anchor: description
                              Binary Binary_Operator.COMP_GT Expression
                                 Type: Boolean
                                 Unary Unary_Operator.STRING_LENGTH Expression
                                    Type: Integer
                                    Name Reference to description
                                 Integer Literal 10
               Package instances
                  Symbol_Table
                     Record_Object SomeThing
                        Type: MyType
                        Field description: "Potato"
               Builtin_Function trlc:endswith
               Builtin_Function trlc:len
               Builtin_Function trlc:matches
               Builtin_Function trlc:startswith
               Builtin_Function endswith
               Builtin_Function len
               Builtin_Function matches
               Builtin_Function startswith

        """
        assert isinstance(indent, int) and indent >= 0
        assert False, "dump not implemented for %s" % self.__class__.__name__


class Check(Node):
    """User defined check

    This represent a single user-defined check inside a check block::

      checks T {
          a /= null implies a > 5, warning "potato", a
          ^^^^^^^^^^^^^^^^^^^^^^^1 ^2      ^3        ^4

    :attribute n_record: The record type this check applies to
    :type: Record_Type

    :attribute n_expr: The boolean expression for the check (see 1)
    :type: Expression

    :attribute n_anchor: The (optional) record component where the message \
    should be issued (or None) (see 4)
    :type: Record_Component

    :attribute severity: warning, error, or fatal (see 2; also if this is \
    not specified the default is 'error')
    :type: str

    :attribute message: the user-supplied message (see 3)
    :type: str
    """
    def __init__(self, n_record, n_expr, n_anchor, severity, t_message):
        assert isinstance(n_record, Record_Type)
        assert isinstance(n_expr, Expression)
        assert isinstance(n_anchor, Record_Component) or n_anchor is None
        assert severity in ("warning", "error", "fatal")
        assert isinstance(t_message, Token)
        assert t_message.kind == "STRING"
        super().__init__(t_message.location)

        self.n_record = n_record
        self.n_expr   = n_expr
        self.n_anchor = n_anchor
        self.severity = severity
        self.message  = t_message.value

    def dump(self, indent=0):  # pragma: no cover
        if self.severity == "warning":
            self.write_indent(indent, "Warning '%s'" % self.message)
        elif self.severity == "error":
            self.write_indent(indent, "Error '%s'" % self.message)
        else:
            self.write_indent(indent, "Fatal error '%s'" % self.message)
        if self.n_anchor:
            self.write_indent(indent + 1, "Anchor: %s" % self.n_anchor.name)
        self.n_expr.dump(indent + 1)

    def get_real_location(self, record_object):
        assert isinstance(record_object, Record_Object)
        if self.n_anchor is None:
            return record_object.location
        elif record_object.field[self.n_anchor.name] is not None:
            return record_object.field[self.n_anchor.name].location
        else:
            return record_object.location

    def perform(self, mh, record_object):
        assert isinstance(mh, Message_Handler)
        assert isinstance(record_object, Record_Object)

        result = self.n_expr.evaluate(mh, copy(record_object.field))
        assert isinstance(result.value, bool)

        if not result.value:
            loc = self.get_real_location(record_object)
            if self.severity == "warning":
                mh.warning(loc,
                           self.message,
                           user = True)
            else:
                mh.error(loc,
                         self.message,
                         fatal = self.severity == "fatal",
                         user  = True)
                return False

        return True

##############################################################################
# AST Nodes (Expressions)
##############################################################################


class Unary_Operator(Enum):
    MINUS          = auto()
    PLUS           = auto()
    LOGICAL_NOT    = auto()
    ABSOLUTE_VALUE = auto()

    STRING_LENGTH  = auto()
    ARRAY_LENGTH   = auto()


class Binary_Operator(Enum):
    LOGICAL_AND     = auto()    # Short-circuit
    LOGICAL_OR      = auto()    # Short-circuit
    LOGICAL_XOR     = auto()
    LOGICAL_IMPLIES = auto()    # Short-circuit

    COMP_EQ  = auto()
    COMP_NEQ = auto()
    COMP_LT  = auto()
    COMP_LEQ = auto()
    COMP_GT  = auto()
    COMP_GEQ = auto()

    STRING_CONTAINS   = auto()
    STRING_STARTSWITH = auto()
    STRING_ENDSWITH   = auto()
    STRING_REGEX      = auto()

    PLUS      = auto()
    MINUS     = auto()
    TIMES     = auto()
    DIVIDE    = auto()
    REMAINDER = auto()

    POWER = auto()

    INDEX = auto()


class Expression(Node):
    """Abstract base class for all expressions.

    :attribute typ: The type of this expression (or None for null values)
    :type: Type
    """
    def __init__(self, location, typ):
        super().__init__(location)
        assert typ is None or isinstance(typ, Type)
        self.typ = typ

    def evaluate(self, mh, context):  # pragma: no cover
        """Evaluate the expression in the given context

        The context can be None, in which case the expression is
        evaluated in a static context. Otherwise it must be a
        dictionary that maps names (such as record fields or
        quantified variables) to expressions.

        :param mh: the message handler to use
        :type mh: Message_Handler
        :param context: name mapping or None (for a static context)
        :type context: dict[str] Expression
        :raise TRLC_Error: if the expression cannot be evaluated
        :return: result of the evaluation
        :rtype: Value
        """
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)
        assert False, "evaluate not implemented for %s" % \
            self.__class__.__name__

    def to_string(self):  # pragma: no cover
        assert False, "to_string not implemented for %s" % \
            self.__class__.__name__

    def ensure_type(self, mh, typ):
        assert isinstance(typ, type)
        if not isinstance(self.typ, typ):
            mh.error(self.location,
                     "expected expression of type %s, got %s instead" %
                     (typ.__name__,
                      self.typ.__class__.__name__))

    def resolve_references(self, mh):
        assert isinstance(mh, Message_Handler)


class Implicit_Null(Expression):
    """Synthesised null values

    When a record object is declared and an optional component is not
    specified, we synthesise an implicit null expression for this.

    For example given this TRLC type::

      type T {
         x optional Integer
      }

    And this declaration::

      T Potato {}

    Then the field mapping for Potato will be::

      {x: Implicit_Null}

    Each field will get its own implicit null. Further note that this
    implicit null is distinct from the explicit :class:`Null_Literal`
    that can appear in check expressions.

    """
    def __init__(self, record_object, record_component):
        assert isinstance(record_object, Record_Object)
        assert isinstance(record_component, Record_Component)
        super().__init__(record_object.location, None)

    def to_string(self):
        return "null"

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)
        return Value(self.location, None, None)

    def to_python_object(self):
        return None


class Literal(Expression):
    """Abstract base for all Literals

    Does not offer any additional features, but it's a nice way to
    group together all literal types. This is useful if you want to
    check if you are dealing with a literal::

      isinstance(my_expression, Literal)

    """
    def to_python_object(self):
        assert False


class Null_Literal(Literal):
    """The null literal

    This can appear in check expressions::

      a /= null implies a > 5
           ^^^^

    Please note that this is distinct from the :class:`Implicit_Null`
    values that appear in record objects.

    """
    def __init__(self, token):
        assert isinstance(token, Token)
        assert token.kind == "KEYWORD"
        assert token.value == "null"
        super().__init__(token.location, None)

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Null Literal")

    def to_string(self):
        return "null"

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)
        return Value(self.location, None, None)

    def to_python_object(self):
        return None


class Integer_Literal(Literal):
    """Integer literals

    Note that these are always positive. A negative integer is
    actually a unary negation expression, operating on a positive
    integer literal::

      x == -5

    This would create the following tree::

       OP_EQUALITY
          NAME_REFERENCE x
          UNARY_EXPRESSION -
             INTEGER_LITERAL 5

    :attribute value: the non-negative integer value
    :type: int
    """
    def __init__(self, token, typ):
        assert isinstance(token, Token)
        assert token.kind == "INTEGER"
        assert isinstance(typ, Builtin_Integer)
        super().__init__(token.location, typ)

        self.value = token.value

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Integer Literal %u" % self.value)

    def to_string(self):
        return str(self.value)

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)
        return Value(self.location, self.value, self.typ)

    def to_python_object(self):
        return self.value


class String_Literal(Literal):
    """String literals

    Note the value of the string does not include the quotation marks,
    and any escape sequences are fully resolved. For example::

       "foo\\"bar"

    Will have a value of ``foo"bar``.

    :attribute value: string content
    :type: str

    """
    def __init__(self, token, typ):
        assert isinstance(token, Token)
        assert token.kind == "STRING"
        assert isinstance(typ, Builtin_String)
        super().__init__(token.location, typ)

        self.value = token.value

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "String Literal %s" % self.value)

    def to_string(self):
        return self.value

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)
        return Value(self.location, self.value, self.typ)

    def to_python_object(self):
        return self.value


class Boolean_Literal(Literal):
    """Boolean values

    :attribute value: the boolean value
    :type: bool
    """
    def __init__(self, token, typ):
        assert isinstance(token, Token)
        assert token.kind == "KEYWORD"
        assert token.value in ("false", "true")
        assert isinstance(typ, Builtin_Boolean)
        super().__init__(token.location, typ)

        self.value = token.value == "true"

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Boolean Literal %s" % self.value)

    def to_string(self):
        return str(self.value)

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)
        return Value(self.location, self.value, self.typ)

    def to_python_object(self):
        return self.value


class Enumeration_Literal(Literal):
    """Enumeration values

    Note that this is distinct from
    :class:`Enumeration_Literal_Spec`. An enumeration literal is a
    specific mention of an enumeration member in an expression::

       foo != my_enum.POTATO
              ^^^^^^^^^^^^^^

    To get to the string value of the enumeration literal
    (i.e. ``POTATO`` here) you can get the name of the literal spec
    itself: ``enum_lit.value.name``; and to get the name of the
    enumeration (i.e. ``my_enum`` here) you can use
    ``enum_lit.value.enum.name``.

    :attribute value: enumeration value
    :type: Enumeration_Literal_Spec

    """
    def __init__(self, location, literal):
        assert isinstance(literal, Enumeration_Literal_Spec)
        super().__init__(location, literal.enum)

        self.value = literal

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent,
                          "Enumeration Literal %s.%s" % (self.typ.name,
                                                         self.value.name))

    def to_string(self):
        return self.typ.name + "." + self.value.name

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)
        return Value(self.location, self.value, self.typ)

    def to_python_object(self):
        return self.value.name


class Array_Aggregate(Expression):
    """Instances of array types

    This is created when assigning to array components::

       potatoes = ["picasso", "yukon gold", "sweet"]
                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    The type of expression that can be found in an array is somewhat
    limited:

    * :class:`Literal`
    * :class:`Array_Aggregate`
    * :class:`Record_Reference`

    :attribute value: contents of the array
    :type: list[Expression]

    """
    def __init__(self, location, typ):
        super().__init__(location, typ)
        self.value = []

    def append(self, value):
        assert isinstance(value, (Literal,
                                  Array_Aggregate,
                                  Record_Reference))
        self.value.append(value)

    def to_string(self):
        return "[" + ", ".join(x.to_string() for x in self.value) + "]"

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)
        return Value(self.location,
                     list(element.evaluate(mh, context)
                          for element in self.value),
                     self.typ)

    def resolve_references(self, mh):
        assert isinstance(mh, Message_Handler)

        for val in self.value:
            val.resolve_references(mh)

    def to_python_object(self):
        return [x.to_python_object() for x in self.value]


class Record_Reference(Expression):
    """Reference to another record object

    This can appear in record object declarations::

      Requirement Kitten {
          depends_on = Other_Package.Cat
                       ^1            ^2
      }

    Note that this is distinct from :class:`Record_Object`. It is just
    the name; to get to the object referred to by this you can consult
    the target attribute.

    The reason we have this indirection is that not all names can be
    immediately resolved on parsing in the TRLC language.

    Note that while the containing package (see 1) is optional in the
    source language, the containing package will always be filled in
    in this AST node.

    :attribute name: The name of the record (see 2)
    :type: str

    :attribute target: The concrete record object referred to by (2)
    :type: Record_Object

    :attribute package: The package (see 1) supposed to contain (2)
    :type: Package

    """
    def __init__(self, referencing_token, typ, package):
        assert isinstance(referencing_token, Token)
        assert referencing_token.kind == "IDENTIFIER"
        assert isinstance(typ, Record_Type)
        assert isinstance(package, Package)
        super().__init__(referencing_token.location, typ)

        self.name    = referencing_token.value
        self.target  = None
        self.package = package

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Record Reference %s" % self.name)
        self.write_indent(indent + 1, "Resolved: %s" % self.target is not None)

    def to_string(self):
        return self.name

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)
        return Value(self.location, self, self.typ)

    def resolve_references(self, mh):
        assert isinstance(mh, Message_Handler)

        self.target = self.package.symbols.lookup_direct(
            mh                = mh,
            name              = self.name,
            error_location    = self.location,
            required_subclass = Record_Object)

    def to_python_object(self):
        return self.name


class Name_Reference(Expression):
    """Reference to a name

    Name reference to either a :class:`Record_Component` or a
    :class:`Quantified_Variable`. The actual value of course depends
    on the context. See :py:meth:`Expression.evaluate()`.

    For example::

      (forall x in potato => x > 1)
                   ^1        ^2

    Both indicated parts are a :class:`Name_Reference`, the first one
    refers to a :class:`Record_Component`, and the second refers to a
    :class:`Quantified_Variable`.

    :attribute entity: the entity named here
    :type: Record_Component, Quantified_Variable
    """
    def __init__(self, location, entity):
        assert isinstance(entity, (Record_Component,
                                   Quantified_Variable))
        super().__init__(location, entity.typ)
        self.entity = entity

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Name Reference to %s" % self.entity.name)

    def to_string(self):
        return self.entity.name

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)

        if context is None:
            mh.error(self.location,
                     "cannot be used in a static context")

        assert self.entity.name in context
        return context[self.entity.name].evaluate(mh, context)


class Unary_Expression(Expression):
    """Expression with only one operand

    This captures the following operations:

    * Unary_Operator.PLUS (e.g. ``+5``)
    * Unary_Operator.MINUS (e.g. ``-5``)
    * Unary_Operator.ABSOLUTE_VALUE (e.g. ``abs 42``)
    * Unary_Operator.LOGICAL_NOT (e.g. ``not True``)
    * Unary_Operator.STRING_LENGTH (e.g. ``len("foobar")``)
    * Unary_Operator.ARRAY_LENGTH (e.g. ``len(component_name)``)

    Note that several builtin functions are mapped to unary operators.

    :attribute operator: the operation
    :type: Unary_Operator

    :attribute n_operand: the expression we operate on
    :type: Expression

    """
    def __init__(self, mh, location, typ, operator, n_operand):
        super().__init__(location, typ)
        assert isinstance(mh, Message_Handler)
        assert isinstance(operator, Unary_Operator)
        assert isinstance(n_operand, Expression)
        self.operator  = operator
        self.n_operand = n_operand

        if operator in (Unary_Operator.MINUS,
                        Unary_Operator.PLUS,
                        Unary_Operator.ABSOLUTE_VALUE):
            self.n_operand.ensure_type(mh, Builtin_Integer)
        elif operator == Unary_Operator.LOGICAL_NOT:
            self.n_operand.ensure_type(mh, Builtin_Boolean)
        elif operator == Unary_Operator.STRING_LENGTH:
            self.n_operand.ensure_type(mh, Builtin_String)
        elif operator == Unary_Operator.ARRAY_LENGTH:
            self.n_operand.ensure_type(mh, Array_Type)
        else:
            mh.ice_loc(self.location,
                       "unexpected unary operation %s" % operator)

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Unary %s Expression" % self.operator)
        self.write_indent(indent + 1, "Type: %s" % self.typ.name)
        self.n_operand.dump(indent + 1)

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)

        v_operand = self.n_operand.evaluate(mh, context)
        if v_operand.value is None:
            mh.error(v_operand.location,
                     "input to unary expression %s (%s) must not be null" %
                     (self.to_string(),
                      self.location.to_string(False)))

        if self.operator == Unary_Operator.MINUS:
            return Value(location = self.location,
                         value    = -v_operand.value,
                         typ      = self.typ)
        elif self.operator == Unary_Operator.PLUS:
            return Value(location = self.location,
                         value    = +v_operand.value,
                         typ      = self.typ)
        elif self.operator == Unary_Operator.LOGICAL_NOT:
            return Value(location = self.location,
                         value    = not v_operand.value,
                         typ      = self.typ)
        elif self.operator == Unary_Operator.ABSOLUTE_VALUE:
            return Value(location = self.location,
                         value    = abs(v_operand.value),
                         typ      = self.typ)
        elif self.operator in (Unary_Operator.STRING_LENGTH,
                               Unary_Operator.ARRAY_LENGTH):
            return Value(location = self.location,
                         value    = len(v_operand.value),
                         typ      = self.typ)
        else:
            mh.ice_loc(self.location,
                       "unexpected unary operation %s" % self.operator)


class Binary_Expression(Expression):
    """Expression with two operands

    This captures the following operations:

    * Binary_Operator.LOGICAL_AND (e.g. ``a and b``)
    * Binary_Operator.LOGICAL_OR (e.g. ``a or b``)
    * Binary_Operator.LOGICAL_XOR (e.g. ``a xor b``)
    * Binary_Operator.LOGICAL_IMPLIES (e.g. ``a implies b``)
    * Binary_Operator.COMP_EQ (e.g. ``a == null``)
    * Binary_Operator.COMP_NEQ (e.g. ``a != null``)
    * Binary_Operator.COMP_LT (e.g. ``1 < 2``)
    * Binary_Operator.COMP_LEQ (e.g. ``1 <= 2``)
    * Binary_Operator.COMP_GT (e.g. ``a > b``)
    * Binary_Operator.COMP_GEQ (e.g. ``a >= b``)
    * Binary_Operator.STRING_CONTAINS (e.g. ``"foo" in "foobar"``)
    * Binary_Operator.STRING_STARTSWITH (e.g. ``startswith("foo", "f")``)
    * Binary_Operator.STRING_ENDSWITH (e.g. ``endswith("foo", "o")``)
    * Binary_Operator.STRING_REGEX (e.g. ``matches("foo", ".o.``)
    * Binary_Operator.PLUS (e.g. ``42 + b`` or ``"foo" + bar``)
    * Binary_Operator.MINUS (e.g. ``a - 1``)
    * Binary_Operator.TIMES (e.g. ``2 * x``)
    * Binary_Operator.DIVIDE (e.g. ``x / 2``)
    * Binary_Operator.REMAINDER (e.g. ``x % 2``)
    * Binary_Operator.POWER (e.g. ``x ** 2``)
    * Binary_Operator.INDEX (e.g. ``foo[2]``)

    Note that several builtin functions are mapped to unary operators.

    Note also that the plus operation is supported for both integers
    and strings.

    :attribute operator: the operation
    :type: Binary_Operator

    :attribute n_lhs: the first operand
    :type: Expression

    :attribute n_lhs: the second operand
    :type: Expression

    """
    def __init__(self, mh, location, typ, operator, n_lhs, n_rhs):
        super().__init__(location, typ)
        assert isinstance(mh, Message_Handler)
        assert isinstance(operator, Binary_Operator)
        assert isinstance(n_lhs, Expression)
        assert isinstance(n_rhs, Expression)
        self.operator = operator
        self.n_lhs    = n_lhs
        self.n_rhs    = n_rhs

        if operator in (Binary_Operator.LOGICAL_AND,
                        Binary_Operator.LOGICAL_OR,
                        Binary_Operator.LOGICAL_XOR,
                        Binary_Operator.LOGICAL_IMPLIES):
            self.n_lhs.ensure_type(mh, Builtin_Boolean)
            self.n_rhs.ensure_type(mh, Builtin_Boolean)

        elif operator in (Binary_Operator.COMP_EQ,
                          Binary_Operator.COMP_NEQ):
            if (self.n_lhs.typ is None) or (self.n_rhs.typ is None):
                # We can compary anything to null (including itself)
                pass
            elif self.n_lhs.typ != self.n_rhs.typ:
                # Otherwise we can compare anything, as long as the
                # types match
                mh.error(self.location,
                         "type mismatch: %s and %s do not match" %
                         (self.n_lhs.typ.name,
                          self.n_rhs.typ.name))

        elif operator in (Binary_Operator.COMP_LT,
                          Binary_Operator.COMP_LEQ,
                          Binary_Operator.COMP_GT,
                          Binary_Operator.COMP_GEQ):
            self.n_lhs.ensure_type(mh, Builtin_Integer)
            self.n_rhs.ensure_type(mh, Builtin_Integer)

        elif operator in (Binary_Operator.STRING_CONTAINS,
                          Binary_Operator.STRING_STARTSWITH,
                          Binary_Operator.STRING_ENDSWITH,
                          Binary_Operator.STRING_REGEX):
            self.n_lhs.ensure_type(mh, Builtin_String)
            self.n_rhs.ensure_type(mh, Builtin_String)

        elif operator == Binary_Operator.PLUS:
            if isinstance(self.n_lhs.typ, Builtin_Integer):
                self.n_rhs.ensure_type(mh, Builtin_Integer)
            else:
                self.n_lhs.ensure_type(mh, Builtin_String)
                self.n_rhs.ensure_type(mh, Builtin_String)

        elif operator in (Binary_Operator.MINUS,
                          Binary_Operator.TIMES,
                          Binary_Operator.DIVIDE,
                          Binary_Operator.REMAINDER,
                          Binary_Operator.POWER):
            self.n_lhs.ensure_type(mh, Builtin_Integer)
            self.n_rhs.ensure_type(mh, Builtin_Integer)

        elif operator == Binary_Operator.INDEX:
            self.n_lhs.ensure_type(mh, Array_Type)
            self.n_rhs.ensure_type(mh, Builtin_Integer)

        else:
            mh.ice_loc(self.location,
                       "unexpected binary operation %s" % operator)

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Binary %s Expression" % self.operator)
        self.write_indent(indent + 1, "Type: %s" % self.typ.name)
        self.n_lhs.dump(indent + 1)
        self.n_rhs.dump(indent + 1)

    def to_string(self):
        infix_operators = {
            Binary_Operator.LOGICAL_AND     : "and",
            Binary_Operator.LOGICAL_OR      : "or",
            Binary_Operator.LOGICAL_XOR     : "xor",
            Binary_Operator.LOGICAL_IMPLIES : "implies",
            Binary_Operator.COMP_EQ         : "==",
            Binary_Operator.COMP_NEQ        : "!=",
            Binary_Operator.COMP_LT         : "<",
            Binary_Operator.COMP_LEQ        : "<=",
            Binary_Operator.COMP_GT         : ">",
            Binary_Operator.COMP_GEQ        : ">=",
            Binary_Operator.STRING_CONTAINS : "in",
            Binary_Operator.PLUS            : "+",
            Binary_Operator.MINUS           : "-",
            Binary_Operator.TIMES           : "*",
            Binary_Operator.DIVIDE          : "/",
            Binary_Operator.REMAINDER       : "%",
            Binary_Operator.POWER           : "**",
        }
        string_functions = {
            Binary_Operator.STRING_STARTSWITH : "startswith",
            Binary_Operator.STRING_ENDSWITH   : "endswith",
            Binary_Operator.STRING_REGEX      : "matches",
        }

        if self.operator in infix_operators:
            return "%s %s %s" % (self.n_lhs.to_string(),
                                 infix_operators[self.operator],
                                 self.n_rhs.to_string())

        elif self.operator in string_functions:
            return "%s(%s, %s)" % (string_functions[self.operator],
                                   self.n_lhs.to_string(),
                                   self.n_rhs.to_string())

        elif self.operator == Binary_Operator.INDEX:
            return "%s[%s]" % (self.n_lhs.to_string(),
                               self.n_rhs.to_string())

        else:
            assert False

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)

        v_lhs = self.n_lhs.evaluate(mh, context)
        if v_lhs.value is None and \
           self.operator not in (Binary_Operator.COMP_EQ,
                                 Binary_Operator.COMP_NEQ):
            mh.error(v_lhs.location,
                     "lhs of check %s (%s) must not be null" %
                     (self.to_string(),
                      self.location.to_string(False)))

        # Check for the short-circuit operators first
        if self.operator == Binary_Operator.LOGICAL_AND:
            assert isinstance(v_lhs.value, bool)
            if v_lhs.value:
                return self.n_rhs.evaluate(mh, context)
            else:
                return v_lhs

        elif self.operator == Binary_Operator.LOGICAL_OR:
            assert isinstance(v_lhs.value, bool)
            if v_lhs.value:
                return v_lhs
            else:
                return self.n_rhs.evaluate(mh, context)

        elif self.operator == Binary_Operator.LOGICAL_IMPLIES:
            assert isinstance(v_lhs.value, bool)
            if v_lhs.value:
                return self.n_rhs.evaluate(mh, context)
            else:
                return Value(location = self.location,
                             value    = True,
                             typ      = self.typ)

        # Otherwise, evaluate RHS and do the operation
        v_rhs = self.n_rhs.evaluate(mh, context)
        if v_rhs.value is None and \
           self.operator not in (Binary_Operator.COMP_EQ,
                                 Binary_Operator.COMP_NEQ):
            mh.error(v_rhs.location,
                     "rhs of check %s (%s) must not be null" %
                     (self.to_string(),
                      self.location.to_string(False)))

        if self.operator == Binary_Operator.LOGICAL_XOR:
            assert isinstance(v_lhs.value, bool)
            assert isinstance(v_rhs.value, bool)
            return Value(location = self.location,
                         value    = v_lhs.value ^ v_rhs.value,
                         typ      = self.typ)

        elif self.operator == Binary_Operator.COMP_EQ:
            return Value(location = self.location,
                         value    = v_lhs.value == v_rhs.value,
                         typ      = self.typ)

        elif self.operator == Binary_Operator.COMP_NEQ:
            return Value(location = self.location,
                         value    = v_lhs.value != v_rhs.value,
                         typ      = self.typ)

        elif self.operator in (Binary_Operator.COMP_LT,
                               Binary_Operator.COMP_LEQ,
                               Binary_Operator.COMP_GT,
                               Binary_Operator.COMP_GEQ):
            return Value(location = self.location,
                         value    = {
                             Binary_Operator.COMP_LT  : lambda l, r: l < r,
                             Binary_Operator.COMP_LEQ : lambda l, r: l <= r,
                             Binary_Operator.COMP_GT  : lambda l, r: l > r,
                             Binary_Operator.COMP_GEQ : lambda l, r: l >= r,
                         }[self.operator](v_lhs.value, v_rhs.value),
                         typ      = self.typ)

        elif self.operator == Binary_Operator.STRING_CONTAINS:
            assert isinstance(v_lhs.value, str)
            assert isinstance(v_rhs.value, str)

            return Value(location = self.location,
                         value    = v_lhs.value in v_rhs.value,
                         typ      = self.typ)

        elif self.operator == Binary_Operator.STRING_STARTSWITH:
            assert isinstance(v_lhs.value, str)
            assert isinstance(v_rhs.value, str)
            return Value(location = self.location,
                         value    = v_lhs.value.startswith(v_rhs.value),
                         typ      = self.typ)

        elif self.operator == Binary_Operator.STRING_ENDSWITH:
            assert isinstance(v_lhs.value, str)
            assert isinstance(v_rhs.value, str)
            return Value(location = self.location,
                         value    = v_lhs.value.endswith(v_rhs.value),
                         typ      = self.typ)

        elif self.operator == Binary_Operator.STRING_REGEX:
            assert isinstance(v_lhs.value, str)
            assert isinstance(v_rhs.value, str)
            return Value(location = self.location,
                         value    = re.match(v_rhs.value,
                                             v_lhs.value) is not None,
                         typ      = self.typ)

        elif self.operator == Binary_Operator.PLUS:
            assert isinstance(v_lhs.value, (int, str))
            assert isinstance(v_rhs.value, (int, str))
            return Value(location = self.location,
                         value    = v_lhs.value + v_rhs.value,
                         typ      = self.typ)

        elif self.operator == Binary_Operator.MINUS:
            assert isinstance(v_lhs.value, int)
            assert isinstance(v_rhs.value, int)
            return Value(location = self.location,
                         value    = v_lhs.value - v_rhs.value,
                         typ      = self.typ)

        elif self.operator == Binary_Operator.TIMES:
            assert isinstance(v_lhs.value, int)
            assert isinstance(v_rhs.value, int)
            return Value(location = self.location,
                         value    = v_lhs.value * v_rhs.value,
                         typ      = self.typ)

        elif self.operator == Binary_Operator.DIVIDE:
            assert isinstance(v_lhs.value, int)
            assert isinstance(v_rhs.value, int)

            if v_rhs.value == 0:
                mh.error(v_rhs.location,
                         "division by zero in %s (%s)" %
                         (self.to_string(),
                          self.location.to_string(False)))

            return Value(location = self.location,
                         value    = v_lhs.value // v_rhs.value,
                         typ      = self.typ)

        elif self.operator == Binary_Operator.REMAINDER:
            assert isinstance(v_lhs.value, int)
            assert isinstance(v_rhs.value, int)

            if v_rhs.value == 0:
                mh.error(v_rhs.location,
                         "division by zero in %s (%s)" %
                         (self.to_string(),
                          self.location.to_string(False)))

            return Value(location = self.location,
                         value    = math.remainder(v_lhs.value, v_rhs.value),
                         typ      = self.typ)

        elif self.operator == Binary_Operator.POWER:
            assert isinstance(v_lhs.value, int)
            assert isinstance(v_rhs.value, int)
            return Value(location = self.location,
                         value    = v_lhs.value ** v_rhs.value,
                         typ      = self.typ)

        elif self.operator == Binary_Operator.INDEX:
            assert isinstance(v_lhs.value, list)
            assert isinstance(v_rhs.value, int)

            if v_rhs.value < 0:
                mh.error(v_rhs.location,
                         "index cannot be less than zero in %s (%s)" %
                         (self.to_string(),
                          self.location.to_string(False)))
            elif v_lhs.typ.upper_bound is not None and \
                 v_rhs.value > v_lhs.typ.upper_bound:
                mh.error(v_rhs.location,
                         "index cannot be more than %u in %s (%s)" %
                         (v_lhs.typ.upper_bound,
                          self.to_string(),
                          self.location.to_string(False)))
            elif v_rhs.value > len(v_lhs.value):
                mh.error(v_lhs.location,
                         "array is not big enough in %s (%s)" %
                         (self.to_string(),
                          self.location.to_string(False)))

            return Value(location = self.location,
                         value    = v_lhs.value[v_rhs.value].value,
                         typ      = self.typ)

        else:
            mh.ice_loc(self.location,
                       "unexpected binary operator %s" % self.operator)


class Range_Test(Expression):
    """Range membership test

    For example in::

      x in 1   ..   field+1
      ^lhs ^lower   ^^^^^^^upper

    Note that none of these are guaranteed to be literals or names;
    you can have arbitrarily complex expressions here.

    :attribute n_lhs: the expression to test
    :type: Expression

    :attribute n_lower: the lower bound
    :type: Expression

    :attribute n_lower: the upper bound
    :type: Expression

    """
    def __init__(self, mh, location, typ, n_lhs, n_lower, n_upper):
        super().__init__(location, typ)
        assert isinstance(mh, Message_Handler)
        assert isinstance(n_lhs, Expression)
        assert isinstance(n_lower, Expression)
        assert isinstance(n_upper, Expression)
        self.n_lhs   = n_lhs
        self.n_lower = n_lower
        self.n_upper = n_upper

        self.n_lhs.ensure_type(mh, Builtin_Integer)
        self.n_lower.ensure_type(mh, Builtin_Integer)
        self.n_upper.ensure_type(mh, Builtin_Integer)

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Range Test")
        self.write_indent(indent + 1, "Type: %s" % self.typ)
        self.n_lhs.dump(indent + 1)
        self.n_lower.dump(indent + 1)
        self.n_upper.dump(indent + 1)

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)

        v_lhs = self.n_lhs.evaluate(mh, context)
        if v_lhs.value is None:
            mh.error(v_lhs.location,
                     "lhs of range check %s (%s) see must not be null" %
                     (self.to_string(),
                      self.location.to_string(False)))

        v_lower = self.n_lower.evaluate(mh, context)
        if v_lower.value is None:
            mh.error(v_lower.location,
                     "lower bound of range check %s (%s) must not be null" %
                     (self.to_string(),
                      self.location.to_string(False)))

        v_upper = self.n_upper.evaluate(mh, context)
        if v_upper.value is None:
            mh.error(v_upper.location,
                     "upper bound of range check %s (%s) must not be null" %
                     (self.to_string(),
                      self.location.to_string(False)))

        return Value(location = self.location,
                     value    = v_lower.value <= v_lhs.value <= v_upper.value,
                     typ      = self.typ)


class Action(Node):
    """An if or elseif part inside a conditional expression

    Each :class:`Conditional_Expression` is made up of a sequence of
    Actions. For example here is a single expression with two
    Actions::

      (if x == 0 then "zero" elsif x == 1 then "one" else "lots")
       ^^^^^^^^^^^^^^^^^^^^^ ^^^^^^^^^^^^^^^^^^^^^^^

    Note that the else part is not an action, it is an attribute of
    the :class:`Conditional_Expression` itself.

    :attribute kind: Either if or elseif
    :type: str

    :attribute n_cond: The boolean condition expression
    :type: Expression

    :attribute n_expr: The value if the condition evaluates to true
    :type: Expression

    """
    def __init__(self, mh, t_kind, n_condition, n_expression):
        assert isinstance(mh, Message_Handler)
        assert isinstance(t_kind, Token)
        assert t_kind.kind == "KEYWORD"
        assert t_kind.value in ("if", "elsif")
        assert isinstance(n_condition, Expression)
        assert isinstance(n_expression, Expression)
        super().__init__(t_kind.location)
        self.kind   = t_kind.value
        self.n_cond = n_condition
        self.n_expr = n_expression

        self.n_cond.ensure_type(mh, Builtin_Boolean)

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "%s Action" % self.kind.capitalize())
        self.write_indent(indent + 1, "Condition")
        self.n_cond.dump(indent + 2)
        self.write_indent(indent + 1, "Value")
        self.n_expr.dump(indent + 2)

    def to_string(self):
        return "%s %s then %s" % (self.kind,
                                  self.n_cond.to_string(),
                                  self.n_expr.to_string())


class Conditional_Expression(Expression):
    """A conditional expression

    Each :class:`Conditional_Expression` is made up of a sequence of
    one or more :class:`Action`. For example here is a single
    expression with two Actions::

      (if x == 0 then "zero" elsif x == 1 then "one" else "lots")
       ^^^^^^^^^^^^^^^^^^^^^ ^^^^^^^^^^^^^^^^^^^^^^^      ^^^^^^

    The else expression is part of the conditional expression itself.

    A conditional expression will have at least one action (the if
    action), and all other actions will be elsif actions. The else
    expression is not optional and will always be present. The types
    of all actions and the else expression will match.

    :attribute actions: a list of Actions
    :type: list[Action]

    :attribute else_expr: the else expression
    :type: Expression

    """
    def __init__(self, location, if_action):
        assert isinstance(if_action, Action)
        assert if_action.kind == "if"
        super().__init__(location, if_action.n_expr.typ)
        self.actions   = [if_action]
        self.else_expr = None

    def add_elsif(self, mh, n_action):
        assert isinstance(mh, Message_Handler)
        assert isinstance(n_action, Action)
        assert n_action.kind == "elsif"

        if n_action.n_expr.typ != self.typ:
            mh.error(n_action.n_expr.location,
                     "expression is of type %s, but must be of type %s" %
                     (n_action.n_expr.typ.name,
                      self.typ.name))

        self.actions.append(n_action)

    def set_else_part(self, mh, n_expr):
        assert isinstance(mh, Message_Handler)
        assert isinstance(n_expr, Expression)

        if n_expr.typ != self.typ:
            mh.error(n_expr.location,
                     "expression is of type %s, but must be of type %s" %
                     (n_expr.typ.name,
                      self.typ.name))

        self.else_expr = n_expr

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Conditional expression")
        for action in self.actions:
            action.dump(indent + 1)
        self.write_indent(indent + 1, "Else")
        self.else_expr.dump(indent + 2)

    def to_string(self):
        rv = "(" + " ".join(action.to_string()
                            for action in self.actions)
        rv += " else %s" % self.else_expr.to_string()
        rv += ")"
        return rv

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)

        for action in self.actions:
            v_cond = action.n_cond.evaluate(mh, context)
            if v_cond.value is None:
                mh.error(v_cond.location,
                         "condition of %s (%s) must not be null" %
                         (action.to_string(),
                          action.location.to_string(False)))
            if v_cond.value:
                return action.n_expr.evaluate(mh, context)

        return self.else_expr.evaluate(mh, context)


class Quantified_Expression(Expression):
    """A quantified expression

    For example::

      (forall x in array_component => x > 0)
              ^1   ^2                 ^^^^^3

    A quantified expression introduces and binds a
    :class:`Quantified_Variable` (see 1) from a specified source (see
    2). When the body (see 3) is evaluated, the name of 1 is bound to
    each component of the source in turn.

    :attribute n_var: The quantified variable (see 1)
    :type: Quantified_Variable

    :attribute n_source: The array to iterate over (see 2)
    :type: Name_Reference

    :attribute n_expr: The body of the quantifier (see 3)
    :type: Expression

    """
    def __init__(self, mh, location, typ, n_variable, n_source, n_expr):
        super().__init__(location, typ)
        assert isinstance(n_variable, Quantified_Variable)
        assert isinstance(n_expr, Expression)
        assert isinstance(n_source, Name_Reference)
        assert isinstance(typ, Builtin_Boolean)
        self.n_var    = n_variable
        self.n_expr   = n_expr
        self.n_source = n_source
        self.n_expr.ensure_type(mh, Builtin_Boolean)

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Quantified expression")
        self.n_var.dump(indent + 1)
        self.n_expr.dump(indent + 1)

    def to_string(self):
        return "(forall %s in %s => %s)" % (self.n_var.name,
                                            self.n_source.to_string(),
                                            self.n_expr.to_string())

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)

        if context is None:
            new_ctx = {}
        else:
            new_ctx = copy(context)

        # This is going to be a bit tricky. We essentially eliminate
        # the quantifier and substitute; for the sake of making better
        # error messages.
        assert isinstance(self.n_source.entity, Record_Component)
        array_values = context[self.n_source.entity.name]
        if isinstance(array_values, Implicit_Null):
            mh.error(array_values.location,
                     "%s in quantified expression %s (%s) "
                     "must not be null" %
                     (self.n_source.to_string(),
                      self.to_string(),
                      self.location.to_string(False)))
        else:
            assert isinstance(array_values, Array_Aggregate)

        ok = True
        loc = self.location
        for binding in array_values.value:
            new_ctx[self.n_var.name] = binding
            result = self.n_expr.evaluate(mh, new_ctx)
            assert isinstance(result.value, bool)
            if not result.value:
                ok  = False
                loc = binding.location
                break

        return Value(location = loc,
                     value    = ok,
                     typ      = self.typ)


##############################################################################
# AST Nodes (Entities)
##############################################################################

class Entity(Node):
    """Base class for all entities.

    An entity is a concrete object (with a name) for which we need to
    allocate memory. Examples of entities are types and record
    objects.

    :attribute name: unqualified name of the entity
    :type: str

    """
    def __init__(self, name, location):
        super().__init__(location)
        assert isinstance(name, str)
        self.name = name


class Quantified_Variable(Entity):
    """Variable used in quantified expression.

    A quantified expression declares and binds a variable, for which
    we need a named entity. For example in::

      (forall x in array => x > 1)
              ^

    We represent this first x as a :class:`Quantified_Variable`, the
    second x will be an ordinary :class:`Name_Reference`.

    :attribute typ: type of the variable (i.e. element type of the array)
    :type: Type

    """
    def __init__(self, name, location, typ):
        super().__init__(name, location)
        assert isinstance(typ, Type)
        self.typ = typ

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Quantified Variable %s" % self.name)
        self.typ.dump(indent + 1)


class Type(Entity):
    """Abstract base class for all types.

    """


class Builtin_Type(Type):
    """Abstract base class for all builtin types.

    """
    LOCATION = Location(file_name = "<builtin>")

    def __init__(self, name):
        super().__init__(name, Builtin_Type.LOCATION)

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, self.__class__.__name__)


class Builtin_Function(Entity):
    """Builtin functions.

    These are auto-generated by the :class:`~trlc.trlc.Source_Manager`.

    :attribute arity: number of parameters
    :type: int

    :attribute deprecated: if this functions is deprecated and should no \
    longer be used
    :type: bool
    """
    LOCATION = Location(file_name = "<builtin>")

    def __init__(self, name, arity):
        super().__init__(name, Builtin_Function.LOCATION)
        assert isinstance(arity, int)
        assert arity >= 0
        self.arity = arity
        self.deprecated = ":" in name

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, self.__class__.__name__ + " " + self.name)


class Array_Type(Type):
    """Anonymous array type.

    These are declared implicitly for each record component that has
    an array specifier::

      foo Integer [5 .. *]
                  ^

    :attribute lower_bound: minimum number of elements
    :type: int

    :attribute upper_bound: maximum number of elements (or None)
    :type: int

    :attribute element_type: type of the array elements
    :type: Type

    """
    def __init__(self, location, element_type, lower_bound, upper_bound):
        assert isinstance(element_type, Type)
        assert isinstance(lower_bound, int)
        assert lower_bound >= 0
        assert upper_bound is None or isinstance(upper_bound, int)
        assert upper_bound is None or upper_bound >= 0

        if upper_bound is None:
            if lower_bound == 0:
                name = "array of %s" % element_type.name
            else:
                name = "array of at least %u %s" % (lower_bound,
                                                    element_type.name)
        elif lower_bound == upper_bound:
            name = "array of %u %s" % (lower_bound,
                                       element_type.name)
        else:
            name = "array of %u to %u %s" % (lower_bound,
                                             upper_bound,
                                             element_type.name)
        super().__init__(name, location)
        self.lower_bound  = lower_bound
        self.upper_bound  = upper_bound
        self.element_type = element_type


class Builtin_Integer(Builtin_Type):
    """Builtin integer type."""
    def __init__(self):
        super().__init__("Integer")


class Builtin_Boolean(Builtin_Type):
    """Builtin boolean type."""
    def __init__(self):
        super().__init__("Boolean")


class Builtin_String(Builtin_Type):
    """Builtin string type."""
    def __init__(self):
        super().__init__("String")


class Package(Entity):
    """Packages.

    A package is declared when it is first encountered (in either a
    rsl or trlc file). A package contains all symbols declared in it,
    both types and record objects. A package is not associated with
    just a single file, it can be spread over multiple files.

    :attribute symbols: symbol table of the package
    :type: Symbol_Table


    """
    def __init__(self, name, location, builtin_stab):
        super().__init__(name, location)
        assert isinstance(builtin_stab, Symbol_Table)
        self.symbols = Symbol_Table()
        self.symbols.make_visible(builtin_stab)
        self.declared_late = False

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Package %s" % self.name)
        self.symbols.dump(indent + 1)


class Record_Type(Type):
    """A user-defined record type.

    In this example::

      type T  "optional description of T" extends Root_T {
           ^1 ^2                         ^3

    :attribute parent: root type or None, indicated by (3) above
    :type: Record_Type

    :attribute components: record components (including inherited)
    :type: Symbol_Table[Record_Component]

    :attribute description: user-supplied description of the record or \
    None, see (2)
    :type: str

    :attribute checks: used-defined checks for this record (excluding \
    inherited checks)
    :type: list[Check]

    """
    def __init__(self, name, description, location, parent=None):
        super().__init__(name, location)
        assert isinstance(description, str) or description is None
        assert isinstance(parent, Record_Type) or parent is None
        self.parent      = parent
        self.components  = Symbol_Table(self.parent.components
                                        if self.parent
                                        else None)
        self.description = description
        self.checks      = []

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Record_Type %s" % self.name)
        if self.description:
            self.write_indent(indent + 1, "Description: %s" % self.description)
        if self.parent:
            self.write_indent(indent + 1, "Parent: %s" % self.parent.name)
        self.components.dump(indent + 1, omit_heading=True)
        if self.checks:
            self.write_indent(indent + 1, "Checks")
            for n_check in self.checks:
                n_check.dump(indent + 2)
        else:
            self.write_indent(indent + 1, "Checks: None")

    def all_components(self):
        """Convenience function to get a list of all components.

        :rtype: list[Record_Component]
        """
        if self.parent:
            return self.parent.all_components() + \
                list(self.components.table.values())
        else:
            return list(self.components.table.values())

    def add_check(self, n_check):
        assert isinstance(n_check, Check)
        self.checks.append(n_check)

    def iter_checks(self):
        if self.parent:
            yield from self.parent.iter_checks()
        yield from self.checks

    def is_subclass_of(self, record_type):
        """ Checks if this record type is or inherits from the given type

        :param record_type: check if are or extend this type
        :type record_type: Record_Type

        :returns: true if we are or extend the given type
        :rtype: Boolean

        """
        assert isinstance(record_type, Record_Type)

        ptr = self
        while ptr:
            if ptr is record_type:
                return True
            else:
                ptr = ptr.parent
        return False


class Record_Component(Entity):
    """Component in a record.

    When declaring a record type, for each component an entity is
    declared::

      type T {
         foo "blah" optional Boolean
         ^1  ^2     ^3       ^4

    :attribute description: optional text (see 2) for this field, or None
    :type: str

    :attribute record: a link back to the containing record; for inherited \
    fields this refers back to the original base record type
    :type: Record_Type

    :attribute typ: type of this component (see 4), but note it could also \
    be an anonymous array type
    :type: Type

    :attribute optional: indicates if the component can be null or not (see 3)
    :type: bool

    """

    def __init__(self, name, description, location, record, typ, optional):
        super().__init__(name, location)
        assert isinstance(description, str) or description is None
        assert isinstance(record, Record_Type)
        assert isinstance(typ, Type)
        assert isinstance(optional, bool)
        self.description = description
        self.record      = record
        self.typ         = typ
        self.optional    = optional

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Record_Component %s" % self.name)
        if self.description:
            self.write_indent(indent + 1, "Description: %s" % self.description)
        self.write_indent(indent + 1, "Optional: %s" % self.optional)
        self.write_indent(indent + 1, "Type: %s" % self.typ.name)


class Enumeration_Type(Type):
    """User-defined enumeration types.

    For example::

      enum T  "potato" {
           ^1 ^2

    :attribute description: user supplied optional description, or None
    :type: str

    :attribute literals: the literals in this enumeration
    :type: Symbol_Table[Enumeration_Literal_Spec]

    """
    def __init__(self, name, description, location):
        super().__init__(name, location)
        assert isinstance(description, str) or description is None
        self.literals    = Symbol_Table()
        self.description = description

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Enumeration_Type %s" % self.name)
        if self.description:
            self.write_indent(indent + 1, "Description: %s" % self.description)
        self.literals.dump(indent + 1, omit_heading=True)


class Enumeration_Literal_Spec(Entity):
    """Declared literal in an enumeration declaration.

    Note that for literals mentioned later in record object
    declarations, we use :class:`Enumeration_Literal`. Literal specs
    are used here::

      enum ASIL {
         QM "not safety related"
         ^1 ^2

    :attribute description: the optional user-supplied description, or None
    :type: str

    :attribute enum: a link back to the declaring enumeration
    :type: Enumeration_Type

    """
    def __init__(self, name, description, location, enum):
        super().__init__(name, location)
        assert isinstance(description, str) or description is None
        assert isinstance(enum, Enumeration_Type)
        self.description = description
        self.enum        = enum

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Enumeration_Literal_Spec %s" % self.name)
        if self.description:
            self.write_indent(indent + 1, "Description: %s" % self.description)


class Record_Object(Entity):
    """A declared instance of a record type.

    This is going to be the bulk of all entities created by TRLC::

       section "Potato" {
               ^5
         Requirement PotatoReq {
         ^1          ^2
             component1 = 42
             ^3           ^4

    Note that the name of the object is provided by the name attribute
    of the :class:`Entity` base class.

    :attribute e_typ: the type of the object (see 1)
    :type: Record_Type

    :attribute field: the specific values for all components (see 3 and 4)
    :type: dict[str] Expression

    :attribute section: None or the section this record is contained in (see 5)
    :type: Section

    The actual type of expressions in the field attribute are limited
    to:

    * :class:`Literal`
    * :class:`Array_Aggregate`
    * :class:`Record_Reference`
    * :class:`Implicit_Null`

    """
    def __init__(self, name, location, e_typ, section):
        super().__init__(name, location)
        assert isinstance(e_typ, Record_Type)
        assert isinstance(section, Section) or section is None
        self.e_typ   = e_typ
        self.field   = {name: None
                        for name in self.e_typ.components.all_names()}
        self.section = section

    def to_python_dict(self):
        """Return an evaluated and simplified object for Python.

        For example it might provide::

          {"foo" : [1, 2, 3],
           "bar" : None,
           "baz" : "value"}

        This is a function especially designed for the Python API. The
        name of the object itself is not in this returned dictionary.

        """
        return {name: value.to_python_object()
                for name, value in self.field.items()}

    def assign(self, component, value):
        assert isinstance(component, Record_Component)
        assert isinstance(value, (Literal,
                                  Array_Aggregate,
                                  Record_Reference,
                                  Implicit_Null))
        self.field[component.name] = value

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Record_Object %s" % self.name)
        self.write_indent(indent + 1, "Type: %s" % self.e_typ.name)
        for key, value in self.field.items():
            self.write_indent(indent + 1,
                              "Field %s: %s" % (key,
                                                repr(value.to_string())))
        if self.section:
            self.section.dump(indent + 1)

    def resolve_references(self, mh):
        assert isinstance(mh, Message_Handler)
        for val in self.field.values():
            val.resolve_references(mh)

    def perform_checks(self, mh):
        assert isinstance(mh, Message_Handler)

        ok = True
        for check in self.e_typ.iter_checks():
            # Prints messages, if applicable. Raises exception on
            # fatal checks, which causes this to abort.
            if not check.perform(mh, self):
                ok = False

        return ok


class Section(Entity):
    """A section for readability

    This represents a section construct in TRLC files to group record
    objects together::

      section "Foo" {
              ^^^^^ parent section
         section "Bar" {
                 ^^^^^ section

    :attribute parent: the parent section or None
    :type: Section

    """
    def __init__(self, name, location, parent):
        super().__init__(name, location)
        assert isinstance(parent, Section) or parent is None
        self.parent  = parent

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Section %s" % self.name)
        if self.parent is None:
            self.write_indent(indent + 1, "Parent: None")
        else:
            self.write_indent(indent + 1, "Parent: %s" % self.parent.name)


##############################################################################
# Symbol Table & Scopes
##############################################################################

class Symbol_Table:
    """ Symbol table mapping names to entities
    """
    def __init__(self, parent=None):
        assert isinstance(parent, Symbol_Table) or parent is None
        self.parent   = parent
        self.imported = []
        self.table    = OrderedDict()

    def all_names(self):
        """ All names in the symbol table

        :rtype: set[str]
        """
        rv = set(self.table)
        if self.parent:
            rv |= self.parent.all_names()
        return rv

    def iter_record_objects(self):
        """ Iterate over all record objects

        :rtype: iterable[Record_Object]
        """
        for item in self.table.values():
            if isinstance(item, Package):
                yield from item.symbols.iter_record_objects()

            elif isinstance(item, Record_Object):
                yield item

    def values(self, subtype=None):
        assert subtype is None or isinstance(subtype, type)
        if self.parent:
            yield from self.parent.values(subtype)
        for name in sorted(self.table):
            if subtype is None or isinstance(self.table[name], subtype):
                yield self.table[name]

    def make_visible(self, stab):
        assert isinstance(stab, Symbol_Table)
        self.imported.append(stab)

    def register(self, mh, entity):
        assert isinstance(mh, Message_Handler)
        assert isinstance(entity, Entity)

        if self.contains(entity.name):
            pdef = self.lookup_direct(mh, entity.name, entity.location)
            mh.error(entity.location,
                     "duplicate definition, previous definition at %s" %
                     pdef.location.to_string(include_column=False))

        else:
            self.table[entity.name] = entity

    def contains(self, name):
        """ Tests if the given name is in the table

        :param name: the name to test
        :type name: str
        :rtype: bool
        """
        assert isinstance(name, str)
        if name in self.table:
            return True
        elif self.parent:
            return self.parent.contains(name)

        for stab in self.imported:
            if stab.contains(name):
                return True

        return False

    def lookup_assuming(self, mh, name, required_subclass=None):
        """Retrieve an object from the table assuming its there

        This is intended for the API specifically where you want to
        e.g. find some used-defined types you know are there.

        :param mh: The message handler to use
        :type mh: Message_Handler

        :param name: The name to search for
        :type name: str

        :param required_subclass: If set, creates an error if the object \
        is not an instance of the given class
        :type required_subclass: type

        :raise TRLC_Error: if the object is not of the required subclass
        :returns: the specified entity (or None if it does not exist)
        :rtype: Entity

        """
        assert isinstance(mh, Message_Handler)
        assert isinstance(name, str)
        assert isinstance(required_subclass, type) or required_subclass is None

        ptr = self
        for ptr in [self] + self.imported:
            while ptr:
                if name in ptr.table:
                    rv = ptr.table[name]
                    if required_subclass is not None and \
                       not isinstance(rv, required_subclass):
                        mh.error(rv.location,
                                 "%s %s is not a %s" %
                                 (rv.__class__.__name__,
                                  name,
                                  required_subclass.__name__))
                    return rv
                else:
                    ptr = ptr.parent

        return None

    def lookup_direct(self, mh, name, error_location, required_subclass=None):
        """Retrieve an object from the table

        For example::

          pkg = stab.lookup_direct(mh,
                                   "potato",
                                   Location("foobar.txt", 42),
                                   Package)

        This would search for an object named ``potato``. If it is
        found, and it is a package, it is returned. If it is not a
        Package, then the following error is issued::

          foobar.txt:42: error: Enumeration_Type potato is not a Package

        If it is not found at all, then the following error is issued::

          foobar.txt:42: error: unknown symbol potato

        :param mh: The message handler to use
        :type mh: Message_Handler

        :param name: The name to search for
        :type name: str

        :param error_location: Where to create the error if the name is \
        not found
        :type error_location: Location

        :param required_subclass: If set, creates an error if the object \
        is not an instance of the given class
        :type required_subclass: type

        :raise TRLC_Error: if the name is not in the table
        :raise TRLC_Error: if the object is not of the required subclass
        :returns: the specified entity
        :rtype: Entity

        """
        assert isinstance(mh, Message_Handler)
        assert isinstance(name, str)
        assert isinstance(error_location, Location)
        assert isinstance(required_subclass, type) or required_subclass is None

        ptr     = self
        options = []
        for ptr in [self] + self.imported:
            while ptr:
                if name in ptr.table:
                    rv = ptr.table[name]
                    if required_subclass is not None and \
                       not isinstance(rv, required_subclass):
                        mh.error(error_location,
                                 "%s %s is not a %s" %
                                 (rv.__class__.__name__,
                                  name,
                                  required_subclass.__name__))
                    return rv
                else:
                    options += list(ptr.table)
                    ptr      = ptr.parent

        matches = get_close_matches(
            word          = name,
            possibilities = options,
            n             = 1)
        if matches:
            mh.error(error_location,
                     "unknown symbol %s, did you mean %s?" %
                     (name,
                      matches[0]))
        else:
            mh.error(error_location,
                     "unknown symbol %s" % name)

    def lookup(self, mh, referencing_token, required_subclass=None):
        assert isinstance(mh, Message_Handler)
        assert isinstance(referencing_token, Token)
        assert referencing_token.kind in ("IDENTIFIER", "BUILTIN")
        assert isinstance(required_subclass, type) or required_subclass is None

        return self.lookup_direct(
            mh                = mh,
            name              = referencing_token.value,
            error_location    = referencing_token.location,
            required_subclass = required_subclass)

    def write_indent(self, indent, message):
        assert isinstance(indent, int)
        assert indent >= 0
        assert isinstance(message, str)
        print(" " * (3 * indent) + message)

    def dump(self, indent=0, omit_heading=False):  # pragma: no cover
        if omit_heading:
            new_indent = indent
        else:
            self.write_indent(indent, "Symbol_Table")
            new_indent = indent + 1
        ptr = self
        while ptr:
            for name in ptr.table:
                ptr.table[name].dump(new_indent)
            ptr = ptr.parent

    @classmethod
    def create_global_table(cls, mh):
        stab = Symbol_Table()
        stab.register(mh, Builtin_Integer())
        stab.register(mh, Builtin_Boolean())
        stab.register(mh, Builtin_String())
        # The legacy versions
        stab.register(mh,
                      Builtin_Function("trlc:len", 1))
        stab.register(mh,
                      Builtin_Function("trlc:startswith", 2))
        stab.register(mh,
                      Builtin_Function("trlc:endswith", 2))
        stab.register(mh,
                      Builtin_Function("trlc:matches", 2))

        # The new-style functions
        stab.register(mh,
                      Builtin_Function("len", 1))
        stab.register(mh,
                      Builtin_Function("startswith", 2))
        stab.register(mh,
                      Builtin_Function("endswith", 2))
        stab.register(mh,
                      Builtin_Function("matches", 2))

        return stab


class Scope:
    def __init__(self):
        self.scope = []

    def push(self, stab):
        assert isinstance(stab, Symbol_Table)
        self.scope.append(stab)

    def pop(self):
        self.scope.pop()

    def contains(self, name):
        assert isinstance(name, str)

        for stab in reversed(self.scope):
            if stab.contains(name):
                return True
        return False

    def lookup(self, mh, referencing_token, required_subclass=None):
        assert len(self.scope) >= 1
        assert isinstance(mh, Message_Handler)
        assert isinstance(referencing_token, Token)
        assert referencing_token.kind in ("IDENTIFIER", "BUILTIN")
        assert isinstance(required_subclass, type) or required_subclass is None

        for stab in reversed(self.scope[1:]):
            if stab.contains(referencing_token.value):
                return stab.lookup(mh, referencing_token, required_subclass)
        return self.scope[0].lookup(mh, referencing_token, required_subclass)

    def size(self):
        return len(self.scope)
