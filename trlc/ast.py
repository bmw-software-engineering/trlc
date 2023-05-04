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

from copy import copy
from difflib import get_close_matches
from enum import Enum, auto
from collections import OrderedDict
from fractions import Fraction

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
    :type: str, int, bool, fractions.Fraction, list[Value], \
    Record_Reference, Enumeration_Literal_Spec

    :attribute typ: type of the value (or None for null values)
    :type: Type
    """
    def __init__(self, location, value, typ):
        assert isinstance(location, Location)
        assert value is None or \
            isinstance(value, (str,
                               int,
                               bool,
                               list,  # for arrays
                               dict,  # for tuples
                               Fraction,
                               Record_Reference,
                               Enumeration_Literal_Spec))
        assert typ is None or isinstance(typ, Type)
        assert (typ is None) == (value is None)

        self.location = location
        self.value    = value
        self.typ      = typ

    def __eq__(self, other):
        return self.typ == other.typ and self.value == other.value

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
               Builtin_Decimal
               Builtin_String
               Builtin_Markup_String
               Package bar
                  Symbol_Table
                     Record_Type MyType
                        Composite_Component name
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

    :attribute n_type: The tuple/record type this check applies to
    :type: Composite_Type

    :attribute n_expr: The boolean expression for the check (see 1)
    :type: Expression

    :attribute n_anchor: The (optional) record component where the message \
    should be issued (or None) (see 4)
    :type: Composite_Component

    :attribute severity: warning, error, or fatal (see 2; also if this is \
    not specified the default is 'error')
    :type: str

    :attribute message: the user-supplied message (see 3)
    :type: str
    """
    def __init__(self, n_type, n_expr, n_anchor, severity, t_message):
        assert isinstance(n_type, Composite_Type)
        assert isinstance(n_expr, Expression)
        assert isinstance(n_anchor, Composite_Component) or n_anchor is None
        assert severity in ("warning", "error", "fatal")
        assert isinstance(t_message, Token)
        assert t_message.kind == "STRING"
        super().__init__(t_message.location)

        self.n_type   = n_type
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

    def get_real_location(self, composite_object):
        assert isinstance(composite_object, (Record_Object,
                                             Tuple_Aggregate))
        if isinstance(composite_object, Record_Object):
            fields = composite_object.field
        else:
            fields = composite_object.value

        if self.n_anchor is None or fields[self.n_anchor.name] is None:
            return composite_object.location
        else:
            return fields[self.n_anchor.name].location

    def perform(self, mh, composite_object):
        assert isinstance(mh, Message_Handler)
        assert isinstance(composite_object, (Record_Object,
                                             Tuple_Aggregate))

        if isinstance(composite_object, Record_Object):
            result = self.n_expr.evaluate(mh, copy(composite_object.field))
        else:
            result = self.n_expr.evaluate(mh, copy(composite_object.value))
        assert isinstance(result.value, bool)

        if not result.value:
            loc = self.get_real_location(composite_object)
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

    CONVERSION_TO_INT     = auto()
    CONVERSION_TO_DECIMAL = auto()


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

    ARRAY_CONTAINS = auto()

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
        :type context: dict[str, Expression]
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
        assert isinstance(typ, (type, Type))
        if isinstance(typ, type) and not isinstance(self.typ, typ):
            mh.error(self.location,
                     "expected expression of type %s, got %s instead" %
                     (typ.__name__,
                      self.typ.__class__.__name__))
        elif isinstance(typ, Type) and self.typ != typ:
            mh.error(self.location,
                     "expected expression of type %s, got %s instead" %
                     (typ.name,
                      self.typ.name))

    def resolve_references(self, mh):
        assert isinstance(mh, Message_Handler)


class Implicit_Null(Expression):
    """Synthesised null values

    When a record object or tuple aggregate is declared and an
    optional component or field is not specified, we synthesise an
    implicit null expression for this.

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
    def __init__(self, composite_object, composite_component):
        assert isinstance(composite_object, (Record_Object,
                                             Tuple_Aggregate))
        assert isinstance(composite_component, Composite_Component)
        super().__init__(composite_object.location, None)

    def to_string(self):
        return "null"

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)
        return Value(self.location, None, None)

    def to_python_object(self):
        return None

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Implicit_Null")


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


class Decimal_Literal(Literal):
    """Decimal literals

    Note that these are always positive. A negative decimal is
    actually a unary negation expression, operating on a positive
    decimal literal::

      x == -5.0

    This would create the following tree::

       OP_EQUALITY
          NAME_REFERENCE x
          UNARY_EXPRESSION -
             DECIMAL_LITERAL 5.0

    :attribute value: the non-negative decimal value
    :type: fractions.Fraction
    """
    def __init__(self, token, typ):
        assert isinstance(token, Token)
        assert token.kind == "DECIMAL"
        assert isinstance(typ, Builtin_Decimal)
        super().__init__(token.location, typ)

        self.value = token.value

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Decimal Literal %u" % self.value)

    def to_string(self):
        return str(self.value)

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)
        return Value(self.location, self.value, self.typ)

    def to_python_object(self):
        return float(self.value)


class String_Literal(Literal):
    """String literals

    Note the value of the string does not include the quotation marks,
    and any escape sequences are fully resolved. For example::

       "foo\\"bar"

    Will have a value of ``foo"bar``.

    :attribute value: string content
    :type: str

    :attribute references: resolved references of a markup string
    :type: list[Record_Reference]

    """
    def __init__(self, token, typ):
        assert isinstance(token, Token)
        assert token.kind == "STRING"
        assert isinstance(typ, Builtin_String)
        super().__init__(token.location, typ)

        self.value          = token.value
        self.has_references = isinstance(typ, Builtin_Markup_String)
        self.references     = []

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "String Literal %s" % repr(self.value))
        if self.has_references:
            self.write_indent(indent + 1, "Markup References")
            for ref in self.references:
                ref.dump(indent + 2)

    def to_string(self):
        return self.value

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)
        return Value(self.location, self.value, self.typ)

    def to_python_object(self):
        return self.value

    def resolve_references(self, mh):
        assert isinstance(mh, Message_Handler)
        for ref in self.references:
            ref.resolve_references(mh)


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
    ``enum_lit.value.n_typ.name``.

    :attribute value: enumeration value
    :type: Enumeration_Literal_Spec

    """
    def __init__(self, location, literal):
        assert isinstance(literal, Enumeration_Literal_Spec)
        super().__init__(location, literal.n_typ)

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
                                  Unary_Expression,
                                  Array_Aggregate,
                                  Tuple_Aggregate,
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


class Tuple_Aggregate(Expression):
    """Instances of a tuple

    This is created when assigning to a tuple components. There are
    two forms, the ordinary form::

       coordinate = (12.3, 40.0)
                    ^^^^^^^^^^^^

    And the separator form::

       item = 12345@42
              ^^^^^^^^

    In terms of AST there is no difference, as the separator is only
    syntactic sugar.

    :attribute value: contents of the tuple
    :type: dict[str, Expression]

    """
    def __init__(self, location, typ):
        super().__init__(location, typ)
        self.value = {n_field.name : Implicit_Null(self, n_field)
                      for n_field in self.typ.components.values()}

    def assign(self, field, value):
        assert isinstance(field, str)
        assert isinstance(value, (Literal,
                                  Unary_Expression,
                                  Tuple_Aggregate,
                                  Record_Reference)), \
                "value is %s" % value.__class__.__name__
        assert field in self.typ.components

        self.value[field] = value

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Tuple_Aggregate")
        self.write_indent(indent + 1, "Type: %s" % self.typ.name)
        for n_item in self.typ.iter_sequence():
            if isinstance(n_item, Composite_Component):
                self.value[n_item.name].dump(indent + 1)

    def to_string(self):
        first = True
        if self.typ.has_separators():
            rv = ""
        else:
            rv = "("
        for n_item in self.typ.iter_sequence():
            if isinstance(n_item, Separator):
                rv += " %s " % n_item.token.value
            elif first:
                first = False
            else:
                rv += ", "

            if isinstance(n_item, Composite_Component):
                rv += self.value[n_item.name].to_string()
        if self.typ.has_separators():
            rv = ""
        else:
            rv = ")"
        return rv

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)
        return Value(self.location,
                     {name : element.evaluate(mh, context)
                      for name, element in self.value.items()},
                     self.typ)

    def resolve_references(self, mh):
        assert isinstance(mh, Message_Handler)

        for val in self.value.values():
            val.resolve_references(mh)

    def to_python_object(self):
        return {name: value.to_python_object()
                for name, value in self.value.items()}


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
    def __init__(self, location, name, typ, package):
        assert isinstance(location, Location)
        assert isinstance(name, str)
        assert isinstance(typ, Record_Type) or typ is None
        assert isinstance(package, Package)
        super().__init__(location, typ)

        self.name    = name
        self.target  = None
        self.package = package

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Record Reference %s" % self.name)
        self.write_indent(indent + 1,
                          "Resolved: %s" % (self.target is not None))

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
        if self.typ is None:
            self.typ = self.target.n_typ
        elif not self.target.n_typ.is_subclass_of(self.typ):
            mh.ice_loc(self.location,
                       "on resolving references, types do not match; "
                       "expected %s, got %s" % (self.typ.name,
                                                self.target.n_typ.name))

    def to_python_object(self):
        return self.name


class Name_Reference(Expression):
    """Reference to a name

    Name reference to either a :class:`Composite_Component` or a
    :class:`Quantified_Variable`. The actual value of course depends
    on the context. See :py:meth:`Expression.evaluate()`.

    For example::

      (forall x in potato => x > 1)
                   ^1        ^2

    Both indicated parts are a :class:`Name_Reference`, the first one
    refers to a :class:`Composite_Component`, and the second refers to a
    :class:`Quantified_Variable`.

    :attribute entity: the entity named here
    :type: Composite_Component, Quantified_Variable
    """
    def __init__(self, location, entity):
        assert isinstance(entity, (Composite_Component,
                                   Quantified_Variable))
        super().__init__(location, entity.n_typ)
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
    * Unary_Operator.CONVERSION_TO_INT (e.g. ``Integer(5.3)``)
    * Unary_Operator.CONVERSION_TO_DECIMAL (e.g. ``Decimal(5)``)

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
            self.n_operand.ensure_type(mh, Builtin_Numeric_Type)
        elif operator == Unary_Operator.LOGICAL_NOT:
            self.n_operand.ensure_type(mh, Builtin_Boolean)
        elif operator == Unary_Operator.STRING_LENGTH:
            self.n_operand.ensure_type(mh, Builtin_String)
        elif operator == Unary_Operator.ARRAY_LENGTH:
            self.n_operand.ensure_type(mh, Array_Type)
        elif operator == Unary_Operator.CONVERSION_TO_INT:
            self.n_operand.ensure_type(mh, Builtin_Numeric_Type)
        elif operator == Unary_Operator.CONVERSION_TO_DECIMAL:
            self.n_operand.ensure_type(mh, Builtin_Numeric_Type)
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
                      mh.cross_file_reference(self.location)))

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
        elif self.operator == Unary_Operator.CONVERSION_TO_INT:
            if isinstance(v_operand.value, Fraction):
                return Value(
                    location = self.location,
                    value    = math.round_nearest_away(v_operand.value),
                    typ      = self.typ)
            else:
                return Value(location = self.location,
                             value    = v_operand.value,
                             typ      = self.typ)
        elif self.operator == Unary_Operator.CONVERSION_TO_DECIMAL:
            return Value(location = self.location,
                         value    = Fraction(v_operand.value),
                         typ      = self.typ)
        else:
            mh.ice_loc(self.location,
                       "unexpected unary operation %s" % self.operator)

    def to_python_object(self):
        assert self.operator in (Unary_Operator.MINUS,
                                 Unary_Operator.PLUS)
        val = self.n_operand.to_python_object()
        if self.operator == Unary_Operator.MINUS:
            return -val
        else:
            return val


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
    * Binary_Operator.ARRAY_CONTAINS (e.g. ``42 in arr``)
    * Binary_Operator.PLUS (e.g. ``42 + b`` or ``"foo" + bar``)
    * Binary_Operator.MINUS (e.g. ``a - 1``)
    * Binary_Operator.TIMES (e.g. ``2 * x``)
    * Binary_Operator.DIVIDE (e.g. ``x / 2``)
    * Binary_Operator.REMAINDER (e.g. ``x % 2``)
    * Binary_Operator.POWER (e.g. ``x ** 2``)
    * Binary_Operator.INDEX (e.g. ``foo[2]``)

    Note that several builtin functions are mapped to unary operators.

    Note also that the plus operation is supported for integers,
    rationals and strings.

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
            self.n_lhs.ensure_type(mh, Builtin_Numeric_Type)
            self.n_rhs.ensure_type(mh, self.n_lhs.typ)

        elif operator in (Binary_Operator.STRING_CONTAINS,
                          Binary_Operator.STRING_STARTSWITH,
                          Binary_Operator.STRING_ENDSWITH,
                          Binary_Operator.STRING_REGEX):
            self.n_lhs.ensure_type(mh, Builtin_String)
            self.n_rhs.ensure_type(mh, Builtin_String)

        elif operator == Binary_Operator.ARRAY_CONTAINS:
            self.n_rhs.ensure_type(mh, Array_Type)
            self.n_lhs.ensure_type(mh, self.n_rhs.typ.element_type.__class__)

        elif operator == Binary_Operator.PLUS:
            if isinstance(self.n_lhs.typ, Builtin_Numeric_Type):
                self.n_rhs.ensure_type(mh, self.n_lhs.typ)
            else:
                self.n_lhs.ensure_type(mh, Builtin_String)
                self.n_rhs.ensure_type(mh, Builtin_String)

        elif operator in (Binary_Operator.MINUS,
                          Binary_Operator.TIMES,
                          Binary_Operator.DIVIDE):
            self.n_lhs.ensure_type(mh, Builtin_Numeric_Type)
            self.n_rhs.ensure_type(mh, self.n_lhs.typ)

        elif operator == Binary_Operator.POWER:
            self.n_lhs.ensure_type(mh, Builtin_Numeric_Type)
            self.n_rhs.ensure_type(mh, Builtin_Integer)

        elif operator == Binary_Operator.REMAINDER:
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
            Binary_Operator.ARRAY_CONTAINS  : "in",
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
                      mh.cross_file_reference(self.location)))

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
                      mh.cross_file_reference(self.location)))

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

        elif self.operator == Binary_Operator.ARRAY_CONTAINS:
            assert isinstance(v_rhs.value, list)

            return Value(location = self.location,
                         value    = v_lhs in v_rhs.value,
                         typ      = self.typ)

        elif self.operator == Binary_Operator.PLUS:
            assert isinstance(v_lhs.value, (int, str, Fraction))
            assert isinstance(v_rhs.value, (int, str, Fraction))
            return Value(location = self.location,
                         value    = v_lhs.value + v_rhs.value,
                         typ      = self.typ)

        elif self.operator == Binary_Operator.MINUS:
            assert isinstance(v_lhs.value, (int, Fraction))
            assert isinstance(v_rhs.value, (int, Fraction))
            return Value(location = self.location,
                         value    = v_lhs.value - v_rhs.value,
                         typ      = self.typ)

        elif self.operator == Binary_Operator.TIMES:
            assert isinstance(v_lhs.value, (int, Fraction))
            assert isinstance(v_rhs.value, (int, Fraction))
            return Value(location = self.location,
                         value    = v_lhs.value * v_rhs.value,
                         typ      = self.typ)

        elif self.operator == Binary_Operator.DIVIDE:
            assert isinstance(v_lhs.value, (int, Fraction))
            assert isinstance(v_rhs.value, (int, Fraction))

            if v_rhs.value == 0:
                mh.error(v_rhs.location,
                         "division by zero in %s (%s)" %
                         (self.to_string(),
                          mh.cross_file_reference(self.location)))

            if isinstance(v_lhs.value, int):
                return Value(location = self.location,
                             value    = v_lhs.value // v_rhs.value,
                             typ      = self.typ)
            else:
                return Value(location = self.location,
                             value    = v_lhs.value / v_rhs.value,
                             typ      = self.typ)

        elif self.operator == Binary_Operator.REMAINDER:
            assert isinstance(v_lhs.value, int)
            assert isinstance(v_rhs.value, int)

            if v_rhs.value == 0:
                mh.error(v_rhs.location,
                         "division by zero in %s (%s)" %
                         (self.to_string(),
                          mh.cross_file_reference(self.location)))

            return Value(location = self.location,
                         value    = math.remainder(v_lhs.value, v_rhs.value),
                         typ      = self.typ)

        elif self.operator == Binary_Operator.POWER:
            assert isinstance(v_lhs.value, (int, Fraction))
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
                          mh.cross_file_reference(self.location)))
            elif v_lhs.typ.upper_bound is not None and \
                 v_rhs.value > v_lhs.typ.upper_bound:
                mh.error(v_rhs.location,
                         "index cannot be more than %u in %s (%s)" %
                         (v_lhs.typ.upper_bound,
                          self.to_string(),
                          mh.cross_file_reference(self.location)))
            elif v_rhs.value > len(v_lhs.value):
                mh.error(v_lhs.location,
                         "array is not big enough in %s (%s)" %
                         (self.to_string(),
                          mh.cross_file_reference(self.location)))

            return Value(location = self.location,
                         value    = v_lhs.value[v_rhs.value].value,
                         typ      = self.typ)

        else:
            mh.ice_loc(self.location,
                       "unexpected binary operator %s" % self.operator)


class Field_Access_Expression(Expression):
    """Tuple field access

    For example in::

      foo.bar
      ^1  ^2

    :attribute n_prefix: expression with tuple type (see 1)
    :type: Expression

    :attribute n_field: a tuple field to dereference (see 2)
    :type: Composite_Component

    """
    def __init__(self, mh, location, n_prefix, n_field):
        assert isinstance(mh, Message_Handler)
        assert isinstance(n_prefix, Expression)
        assert isinstance(n_field, Composite_Component)
        super().__init__(location, n_field.n_typ)
        self.n_prefix = n_prefix
        self.n_field  = n_field

        self.n_prefix.ensure_type(mh, self.n_field.member_of)

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Field_Access (%s)" % self.n_field.name)
        self.n_prefix.dump(indent + 1)

    def to_string(self):
        return self.n_prefix.to_string() + "." + self.n_field.name

    def evaluate(self, mh, context):
        assert isinstance(mh, Message_Handler)
        assert context is None or isinstance(context, dict)

        return self.n_prefix.evaluate(mh, context).value[self.n_field.name]


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

        self.n_lhs.ensure_type(mh, Builtin_Numeric_Type)
        self.n_lower.ensure_type(mh, self.n_lhs.typ)
        self.n_upper.ensure_type(mh, self.n_lhs.typ)

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
                      mh.cross_file_reference(self.location)))

        v_lower = self.n_lower.evaluate(mh, context)
        if v_lower.value is None:
            mh.error(v_lower.location,
                     "lower bound of range check %s (%s) must not be null" %
                     (self.to_string(),
                      mh.cross_file_reference(self.location)))

        v_upper = self.n_upper.evaluate(mh, context)
        if v_upper.value is None:
            mh.error(v_upper.location,
                     "upper bound of range check %s (%s) must not be null" %
                     (self.to_string(),
                      mh.cross_file_reference(self.location)))

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
                          mh.cross_file_reference(self.location)))
            if v_cond.value:
                return action.n_expr.evaluate(mh, context)

        return self.else_expr.evaluate(mh, context)


class Quantified_Expression(Expression):
    """A quantified expression

    For example::

      (forall x in array_component => x > 0)
       ^4     ^1   ^2                 ^^^^^3

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

    :attribute universal: True means forall, false means exists (see 4)
    :type: Boolean

    """
    def __init__(self, mh, location,
                 typ,
                 universal,
                 n_variable,
                 n_source,
                 n_expr):
        super().__init__(location, typ)
        assert isinstance(typ, Builtin_Boolean)
        assert isinstance(universal, bool)
        assert isinstance(n_variable, Quantified_Variable)
        assert isinstance(n_expr, Expression)
        assert isinstance(n_source, Name_Reference)
        self.universal = universal
        self.n_var     = n_variable
        self.n_expr    = n_expr
        self.n_source  = n_source
        self.n_expr.ensure_type(mh, Builtin_Boolean)

    def dump(self, indent=0):  # pragma: no cover
        if self.universal:
            self.write_indent(indent, "Universal quantified expression")
        else:
            self.write_indent(indent, "Existential quantified expression")
        self.n_var.dump(indent + 1)
        self.n_expr.dump(indent + 1)

    def to_string(self):
        return "(%s %s in %s => %s)" % ("forall"
                                        if self.universal
                                        else "exists",
                                        self.n_var.name,
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
        assert isinstance(self.n_source.entity, Composite_Component)
        array_values = context[self.n_source.entity.name]
        if isinstance(array_values, Implicit_Null):
            mh.error(array_values.location,
                     "%s in quantified expression %s (%s) "
                     "must not be null" %
                     (self.n_source.to_string(),
                      self.to_string(),
                      mh.cross_file_reference(self.location)))
        else:
            assert isinstance(array_values, Array_Aggregate)

        rv  = self.universal
        loc = self.location
        for binding in array_values.value:
            new_ctx[self.n_var.name] = binding
            result = self.n_expr.evaluate(mh, new_ctx)
            assert isinstance(result.value, bool)
            if self.universal and not result.value:
                rv  = False
                loc = binding.location
                break
            elif not self.universal and result.value:
                rv  = True
                loc = binding.location
                break

        return Value(location = loc,
                     value    = rv,
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


class Typed_Entity(Entity):
    """Base class for entities with a type.

    A typed entity is a concrete object (with a name and TRLC type)
    for which we need to allocate memory. Examples of typed entities
    are record objects and components.

    :attribute n_typ: type of the entity
    :type: Type

    """
    def __init__(self, name, location, n_typ):
        super().__init__(name, location)
        assert isinstance(n_typ, Type)
        self.n_typ = n_typ


class Quantified_Variable(Typed_Entity):
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
    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Quantified Variable %s" % self.name)
        self.n_typ.dump(indent + 1)


class Type(Entity):
    """Abstract base class for all types.

    """
    def perform_type_checks(self, mh, value):
        assert isinstance(mh, Message_Handler)
        assert isinstance(value, Expression)
        return True


class Concrete_Type(Type):
    """Abstract base class for all non-anonymous types.

    :attribute n_package: package where this type was declared
    :type: Package
    """
    def __init__(self, name, location, n_package):
        super().__init__(name, location)
        assert isinstance(n_package, Package)
        self.n_package = n_package

    def fully_qualified_name(self):
        """Return the FQN for this type (i.e. PACKAGE.NAME)

        :returns: the type's full name
        :rtype: str
        """
        return self.n_package.name + "." + self.name

    def __hash__(self):
        return hash((self.n_package.name, self.name))

    def __repr__(self):
        return "%s<%s>" % (self.__class__.__name__,
                           self.fully_qualified_name())


class Builtin_Type(Type):
    """Abstract base class for all builtin types.

    """
    LOCATION = Location(file_name = "<builtin>")

    def __init__(self, name):
        super().__init__(name, Builtin_Type.LOCATION)

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, self.__class__.__name__)


class Builtin_Numeric_Type(Builtin_Type):
    """Abstract base class for all builtin numeric types.

    """
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
        assert isinstance(element_type, Type) or element_type is None
        assert isinstance(lower_bound, int)
        assert lower_bound >= 0
        assert upper_bound is None or isinstance(upper_bound, int)
        assert upper_bound is None or upper_bound >= 0

        if element_type is None:
            name = "universal array"
        elif upper_bound is None:
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

    def perform_type_checks(self, mh, value):
        assert isinstance(mh, Message_Handler)
        if isinstance(value, Array_Aggregate):
            return all(self.element_type.perform_type_checks(mh, v)
                       for v in value.value)
        else:
            assert isinstance(value, Implicit_Null)
            return True


class Builtin_Integer(Builtin_Numeric_Type):
    """Builtin integer type."""
    def __init__(self):
        super().__init__("Integer")


class Builtin_Decimal(Builtin_Numeric_Type):
    """Builtin decimal type."""
    def __init__(self):
        super().__init__("Decimal")


class Builtin_Boolean(Builtin_Type):
    """Builtin boolean type."""
    def __init__(self):
        super().__init__("Boolean")


class Builtin_String(Builtin_Type):
    """Builtin string type."""
    def __init__(self):
        super().__init__("String")


class Builtin_Markup_String(Builtin_String):
    """Builtin string type that allows checked references to TRLC
       objects.
    """
    def __init__(self):
        super().__init__()
        self.name = "Markup_String"


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


class Composite_Type(Concrete_Type):
    """Abstract base for record and tuple types, as they share some
       functionality.

    :attribute components: type components (including inherited if applicable)
    :type: Symbol_Table[Composite_Component]

    :attribute description: user-supplied description of the type or None
    :type: str

    :attribute checks: used-defined checks for this type (excluding \
      inherited checks)
    :type: list[Check]

    """
    def __init__(self,
                 name,
                 description,
                 location,
                 package,
                 inherited_symbols=None):
        super().__init__(name, location, package)
        assert isinstance(description, str) or description is None
        assert isinstance(inherited_symbols, Symbol_Table) or \
            inherited_symbols is None

        self.components  = Symbol_Table(inherited_symbols)
        self.description = description
        self.checks      = []

    def add_check(self, n_check):
        assert isinstance(n_check, Check)
        self.checks.append(n_check)

    def iter_checks(self):
        yield from self.checks


class Composite_Component(Typed_Entity):
    """Component in a record or tuple.

    When declaring a composite type, for each component an entity is
    declared::

      type|tuple T {
         foo "blah" optional Boolean
         ^1  ^2     ^3       ^4

    :attribute description: optional text (see 2) for this component, or None
    :type: str

    :attribute member_of: a link back to the containing record or tuple; \
    for inherited fields this refers back to the original base record type
    :type: Composite_Type

    :attribute optional: indicates if the component can be null or not (see 3)
    :type: bool

    """

    def __init__(self,
                 name,
                 description,
                 location,
                 member_of,
                 n_typ,
                 optional):
        super().__init__(name, location, n_typ)
        assert isinstance(description, str) or description is None
        assert isinstance(member_of, Composite_Type)
        assert isinstance(optional, bool)
        self.description = description
        self.member_of   = member_of
        self.optional    = optional

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Composite_Component %s" % self.name)
        if self.description:
            self.write_indent(indent + 1, "Description: %s" % self.description)
        self.write_indent(indent + 1, "Optional: %s" % self.optional)
        self.write_indent(indent + 1, "Type: %s" % self.n_typ.name)


class Record_Type(Composite_Type):
    """A user-defined record type.

    In this example::

      type T  "optional description of T" extends Root_T {
           ^1 ^2                                  ^3

    Note that (1) is part of the :class:`Entity` base, and (2) is part
    of the :class:`Composite_Type` base.

    :attribute parent: root type or None, indicated by (3) above
    :type: Record_Type

    :attribute frozen: mapping of frozen components
    :type: dict[str, Expression]

    :attribute is_final: type is final (i.e. no new components may be declared)
    :type: bool

    :attribute is_abstract: type is abstract
    :type: bool

    """
    def __init__(self,
                 name,
                 description,
                 location,
                 package,
                 n_parent,
                 is_abstract):
        assert isinstance(n_parent, Record_Type) or n_parent is None
        assert isinstance(is_abstract, bool)
        super().__init__(name,
                         description,
                         location,
                         package,
                         n_parent.components if n_parent else None)
        self.parent      = n_parent
        self.frozen      = {}
        self.is_final    = (n_parent.is_final if n_parent else False)
        self.is_abstract = is_abstract

    def iter_checks(self):
        if self.parent:
            yield from self.parent.iter_checks()
        yield from self.checks

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

        :rtype: list[Composite_Component]
        """
        if self.parent:
            return self.parent.all_components() + \
                list(self.components.table.values())
        else:
            return list(self.components.table.values())

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

    def is_frozen(self, n_component):
        """Test if the given component is frozen.

        :param n_component: a composite component of this record type \
          (or any of its parents)
        :type n_component: Composite_Component

        :rtype: bool
        """
        assert isinstance(n_component, Composite_Component)
        if n_component.name in self.frozen:
            return True
        elif self.parent:
            return self.parent.is_frozen(n_component)
        else:
            return False

    def get_freezing_expression(self, n_component):
        """Retrieve the frozen value for a frozen component

        It is an internal compiler error to call this method with a
        component that his not frozen.

        :param n_component: a frozen component of this record type \
          (or any of its parents)
        :type n_component: Composite_Component

        :rtype: Expression

        """
        assert isinstance(n_component, Composite_Component)
        if n_component.name in self.frozen:
            return self.frozen[n_component.name]
        elif self.parent:
            return self.parent.get_freezing_expression(n_component)
        else:
            assert False


class Tuple_Type(Composite_Type):
    """A user-defined tuple type.

    In this example::

      tuple T  "optional description of T" {
            ^1 ^2

    Note that (1) is part of the :class:`Entity` base, and (2) is part
    of the :class:`Composite_Type` base.

    :attribute separators: list of syntactic separators.
    :type: list[Separator]

    Note the list of separators will either be empty, or there will be
    precisely one less separator than components.

    """
    def __init__(self, name, description, location, package):
        super().__init__(name,
                         description,
                         location,
                         package)
        self.separators = []

    def add_separator(self, n_separator):
        assert isinstance(n_separator, Separator)
        assert len(self.separators) + 1 == len(self.components.table)
        self.separators.append(n_separator)

    def iter_separators(self):
        """Iterate over all separators"""
        yield from self.separators

    def iter_sequence(self):
        """Iterate over all components and separators in syntactic order"""
        if self.separators:
            for i, n_component in enumerate(self.components.table.values()):
                yield n_component
                if i < len(self.separators):
                    yield self.separators[i]
        else:
            yield from self.components.table.values()

    def has_separators(self):
        """Returns true if a tuple type requires separators"""
        return bool(self.separators)

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Tuple_Type %s" % self.name)
        if self.description:
            self.write_indent(indent + 1, "Description: %s" % self.description)
        self.write_indent(indent + 1, "Fields")
        for n_item in self.iter_sequence():
            n_item.dump(indent + 2)
        if self.checks:
            self.write_indent(indent + 1, "Checks")
            for n_check in self.checks:
                n_check.dump(indent + 2)
        else:
            self.write_indent(indent + 1, "Checks: None")

    def perform_type_checks(self, mh, value):
        assert isinstance(mh, Message_Handler)
        if isinstance(value, Tuple_Aggregate):
            ok = True
            for check in self.iter_checks():
                if not check.perform(mh, value):
                    ok = False
            return ok
        else:
            assert isinstance(value, Implicit_Null)
            return True


class Separator(Node):
    """User-defined syntactic separator

    For example::

      separator x
                ^1

    :attribute token: token used to separate fields of the tuple
    :type: Token
    """
    def __init__(self, token):
        super().__init__(token.location)
        assert isinstance(token, Token) and token.kind in ("IDENTIFIER",
                                                           "AT",
                                                           "COLON",
                                                           "SEMICOLON")
        self.token = token

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Separator %s" % self.token.value)


class Enumeration_Type(Concrete_Type):
    """User-defined enumeration types.

    For example::

      enum T  "potato" {
           ^1 ^2

    :attribute description: user supplied optional description, or None
    :type: str

    :attribute literals: the literals in this enumeration
    :type: Symbol_Table[Enumeration_Literal_Spec]

    """
    def __init__(self, name, description, location, package):
        super().__init__(name, location, package)
        assert isinstance(description, str) or description is None
        self.literals    = Symbol_Table()
        self.description = description

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Enumeration_Type %s" % self.name)
        if self.description:
            self.write_indent(indent + 1, "Description: %s" % self.description)
        self.literals.dump(indent + 1, omit_heading=True)


class Enumeration_Literal_Spec(Typed_Entity):
    """Declared literal in an enumeration declaration.

    Note that for literals mentioned later in record object
    declarations, we use :class:`Enumeration_Literal`. Literal specs
    are used here::

      enum ASIL {
         QM "not safety related"
         ^1 ^2

    :attribute description: the optional user-supplied description, or None
    :type: str

    """
    def __init__(self, name, description, location, enum):
        super().__init__(name, location, enum)
        assert isinstance(description, str) or description is None
        assert isinstance(enum, Enumeration_Type)
        self.description = description

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Enumeration_Literal_Spec %s" % self.name)
        if self.description:
            self.write_indent(indent + 1, "Description: %s" % self.description)


class Record_Object(Typed_Entity):
    """A declared instance of a record type.

    This is going to be the bulk of all entities created by TRLC::

       section "Potato" {
               ^5
         Requirement PotatoReq {
         ^1          ^2
             component1 = 42
             ^3           ^4

    Note that the name (see 2) and type (see 1) of the object is
    provided by the name attribute of the :class:`Typed_Entity` base
    class.

    :attribute field: the specific values for all components (see 3 and 4)
    :type: dict[str, Expression]

    :attribute section: None or the section this record is contained in (see 5)
    :type: Section

    The actual type of expressions in the field attribute are limited
    to:

    * :class:`Literal`
    * :class:`Unary_Expression`
    * :class:`Array_Aggregate`
    * :class:`Tuple_Aggregate`
    * :class:`Record_Reference`
    * :class:`Implicit_Null`

    """
    def __init__(self, name, location, n_typ, section):
        assert isinstance(n_typ, Record_Type)
        assert isinstance(section, Section) or section is None
        super().__init__(name, location, n_typ)
        self.field   = {name: None
                        for name in self.n_typ.components.all_names()}
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
        assert isinstance(component, Composite_Component)
        assert isinstance(value, (Literal,
                                  Array_Aggregate,
                                  Tuple_Aggregate,
                                  Record_Reference,
                                  Implicit_Null,
                                  Unary_Expression)), \
                "value is %s" % value.__class__.__name__
        self.field[component.name] = value

    def dump(self, indent=0):  # pragma: no cover
        self.write_indent(indent, "Record_Object %s" % self.name)
        self.write_indent(indent + 1, "Type: %s" % self.n_typ.name)
        for key, value in self.field.items():
            self.write_indent(indent + 1, "Field %s" % key)
            value.dump(indent + 2)
        if self.section:
            self.section.dump(indent + 1)

    def resolve_references(self, mh):
        assert isinstance(mh, Message_Handler)
        for val in self.field.values():
            val.resolve_references(mh)

    def perform_checks(self, mh):
        assert isinstance(mh, Message_Handler)

        ok = True

        # First evaluate all tuple checks
        for n_comp in self.n_typ.all_components():
            if not n_comp.n_typ.perform_type_checks(mh,
                                                    self.field[n_comp.name]):
                ok = False

        # Then evaluate all record checks
        for check in self.n_typ.iter_checks():
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
                     mh.cross_file_reference(pdef.location))

        else:
            self.table[entity.name] = entity

    def __contains__(self, name):
        return self.contains(name)

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

    def write_indent(self, indent, message):  # pragma: no cover
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
        stab.register(mh, Builtin_Decimal())
        stab.register(mh, Builtin_Boolean())
        stab.register(mh, Builtin_String())
        stab.register(mh, Builtin_Markup_String())
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
