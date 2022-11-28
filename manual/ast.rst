:tocdepth: 3

AST
===

Root class
----------

.. autoclass:: trlc.ast.Node
   :exclude-members:

Entities
--------

.. autoclass:: trlc.ast.Entity

.. autoclass:: trlc.ast.Quantified_Variable

.. autoclass:: trlc.ast.Builtin_Function

.. autoclass:: trlc.ast.Package

.. autoclass:: trlc.ast.Check

.. autoclass:: trlc.ast.Record_Component

.. autoclass:: trlc.ast.Enumeration_Literal_Spec

.. autoclass:: trlc.ast.Record_Object

.. autoclass:: trlc.ast.Section

Types
-----

.. autoclass:: trlc.ast.Type

.. autoclass:: trlc.ast.Array_Type

.. autoclass:: trlc.ast.Builtin_Integer

.. autoclass:: trlc.ast.Builtin_String

.. autoclass:: trlc.ast.Builtin_Boolean

.. autoclass:: trlc.ast.Record_Type

.. autoclass:: trlc.ast.Enumeration_Type

Expressions
-----------

.. autoclass:: trlc.ast.Expression
   :exclude-members: dump

.. autoclass:: trlc.ast.Implicit_Null

.. autoclass:: trlc.ast.Array_Aggregate

.. autoclass:: trlc.ast.Record_Reference

.. autoclass:: trlc.ast.Name_Reference

.. autoclass:: trlc.ast.Unary_Expression

.. autoclass:: trlc.ast.Binary_Expression

.. autoclass:: trlc.ast.Range_Test

.. autoclass:: trlc.ast.Action

.. autoclass:: trlc.ast.Conditional_Expression

.. autoclass:: trlc.ast.Quantified_Expression

Literals
--------

.. autoclass:: trlc.ast.Literal

.. autoclass:: trlc.ast.Null_Literal

.. autoclass:: trlc.ast.Integer_Literal

.. autoclass:: trlc.ast.String_Literal

.. autoclass:: trlc.ast.Boolean_Literal

.. autoclass:: trlc.ast.Enumeration_Literal

Evaluation
----------

.. autoclass:: trlc.ast.Value

Symbols and scope
-----------------

.. autoclass:: trlc.ast.Symbol_Table
