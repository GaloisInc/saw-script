================
SAW Verification
================

Note: The SAW API is still in flux and is not yet fully documented.

As with the Cryptol methods, server state is propagated as described in the
protocol overview.

Methods implemented against the SAW API may throw :ref:`a variety of SAW-related
errors <saw-server-errors>`, with codes in the range of ``10000``-``19999``.
Additionally, SAW verification relies on Cryptol, and some SAW methods may throw
:ref:`Cryptol server errors <cryptol-server-errors>` when appropriate.

Cryptol Module Management
=========================

Loading Modules
---------------

:Method name:
  ``SAW/Cryptol/load module``
:Parameters:
  - ``module name``: The name of the Cryptol module to be loaded.

Loading Files
-------------

:Method name:
  ``SAW/Cryptol/load file``
:Parameters:
  - ``file``: The name of the Cryptol source file to be loaded.

Saving Terms
------------

:Method name:
  ``SAW/Cryptol/save term``
:Parameters:
  - ``name``: The name to bind the value of ``expression`` to on the server.
  - ``expression``: The Cryptol expression to bind the value of ``name`` to on the server.

JVM Verification
================

NOTE: The following represents an aspirational view of the JVM-specific protocol; currently,
the code underlying these methods is incomplete and does not work.

Loading Classes
---------------

:Method name:
  ``SAW/JVM/load class``
:Parameters:
  - ``name``: The name to bind the loaded class to on the server.
  - ``class``: The name of the class to load and bind the value of ``name`` to on the server.

Verifying
---------

:Method name:
  ``SAW/JVM/verify``
:Parameters:
  - ``module``: The name of the (previously loaded) *class* containing the function/method to verify.
  - ``function``: The name of the function/method to verify.
  - ``lemmas``: A list containing the names of previously proved lemmas to be used in compositional verification.
  - ``check sat``: A Boolean value indicating whether or not to perform path satisfiability checking.
  - ``contract``: The :ref:`specification<specifications>` to perform verification against.
  - ``script``: The :ref:`proof script<proof-scripts>` to use for verification.
  - ``lemma name``: The name to bind the result of verification to on the server.

Assuming
--------

:Method name:
  ``SAW/JVM/assume``
:Parameters:
  - ``module``: The name of the (previously loaded) *class* containing the function/method to assume verified.
  - ``function``: The name of the function/method to assume verified.
  - ``contract``: The :ref:`specification<specifications>` to assume for the given function/method.
  - ``lemma name``: The name to bind the result of verification to on the server.

LLVM Verification
=================

Loading Modules
---------------

:Method name:
  ``SAW/LLVM/load module``
:Parameters:
  - ``name``: The name to bind the loaded bitcode file to on the server.
  - ``bitcode file``: The path to the bitcode file to load and bind to ``name`` on the server.

Verifying (LLVM Implementations)
--------------------------------

:Method name:
  ``SAW/LLVM/verify``
:Parameters:
  - ``module``: The name of the (previously loaded) module containing the function to verify.
  - ``function``: The name of the function to verify.
  - ``lemmas``: A list containing the names of previously proved lemmas to be used in compositional verification.
  - ``check sat``: A Boolean value indicating whether or not to perform path satisfiability checking.
  - ``contract``: The :ref:`specification<specifications>` to perform verification against.
  - ``script``: The :ref:`proof script<proof-scripts>` to use for verification.
  - ``lemma name``: The name to bind the result of verification to on the server.

Verifying (x86 Implementations)
-------------------------------

:Method name:
  ``SAW/LLVM/verify x86``
:Parameters:
  - ``module``: The name of the (previously loaded) module containing the type of the function to verify.
  - ``object file``: The path to the x86 object file containing the implementation of the function to verify.
  - ``function``: The name of the function to verify.
  - ``globals``: A list containing the global allocations needed for the verification task.
  - ``lemmas``: A list containing the names of previously proved lemmas to be used in compositional verification.
  - ``check sat``: A Boolean value indicating whether or not to perform path satisfiability checking.
  - ``contract``: The :ref:`specification<specifications>` to perform verification against.
  - ``script``: The :ref:`proof script<proof-scripts>` to use for verification.
  - ``lemma name``: The name to bind the result of verification to on the server.

Assuming
--------

:Method name:
  ``SAW/LLVM/assume``
:Parameters:
  - ``module``: The name of the (previously loaded) *class* containing the function/method to assume verified.
  - ``function``: The name of the function/method to assume verified.
  - ``contract``: The :ref:`specification<specifications>` to assume for the given function/method.
  - ``lemma name``: The name to bind the result of verification to on the server.

Proof Management
================

Making Simpsets
---------------

:Method name:
  ``SAW/make simpset``
:Parameters:
  - ``elements``: A list of names bound to terms to add to the simpset.
  - ``result``: The name to bind the simpset to on the server.

Running Proof Scripts
---------------------

:Method name:
  ``SAW/prove``
:Parameters:
  - ``script``: The :ref:`proof script<proof-scripts>` to run.
  - ``term``: The name of a term bound on the server to run the proof script against.
:Return fields:
  - ``status``: A string (either ``valid`` or ``invalid``) indicating whether the proof went through successfully or not.

Setting Options
---------------

:Method name:
  ``SAW/set option``
:Parameters:
  - ``option``: The name of the option to set. This is one of:

    * ``lax arithmetic``
    * ``lax pointer ordering``
    * ``SMT array memory model``
    * ``What4 hash consing``

  - ``value``: A Boolean value indicating whether to enable/disable the feature named by ``option``.

.. _specifications:

Specifications
==============

SAW verification relies on the provision of specifications to verify against. In the API,
these specifications are represented by a JSON object with the following fields:

``pre vars``
  A list of symbolic variables introduced in the initial state section of the specification. These variables
  are represented by a JSON object containing three fields:

.. _contract-vars:

  - ``server name``: The name of the variable on the server.
  - ``name``: The "display name" of the variable, used in debugging output.
  - ``type``: The :ref:`LLVM<llvm-types>` or :ref:`JVM<jvm-types>` type of this variable.

``pre conds``
  A list of the specification's preconditions, as :ref:`Cryptol terms<cryptol-json-expression>`.

``pre allocated``
  A list of allocations in the initial state section of the specification. In preconditions,
  allocations specify that the function being verified expects a pointer to the allocated memory
  to exist. An allocation is a JSON object containing four fields, one of which is optional:

.. _allocation:

  - ``server name``: The name by which the allocation is referred to on the server.
  - ``type``: The :ref:`LLVM<llvm-types>` or :ref:`JVM<jvm-types>` type of the data for which space is being allocated.
  - ``mutable``: A Boolean value indicating whether the allocated memory is mutable or not.
  - ``alignment``: An integer value indicating where the start of the allocated memory should
    be aligned. This value must be a power of two, and the allocated memory may be aligned at
    any multiple of it. The field *must* be ``null`` in JVM specifications, and *may* be ``null``
    in LLVM specifications.

``pre points to``
  A list of 'points-to' relationships in the initial state section of the specification. These
  relationships are captured in a JSON object containing four fields, two of which are optional:

.. _points-to:

  - ``pointer``: A :ref:`Crucible Setup value<setup-values>` representing the pointer.
  - ``points to``: A :ref:`Crucible Setup value<setup-values>` representing the referent of ``pointer``.
  - ``check points to type``: An optional description of a type to check the ``points to`` value against.
    If the description is ``null``, then this has no effect. The description is represented as a JSON
    object containing a tag named ``check against``, with any further fields determined by this tag.
    These tag values can be:

    + ``pointer type``: Check the type of the ``points to`` value against the type that the ``pointer``
      value's type points to.
    + ``casted type``: Check the type of the ``points to`` value against the provided type. There is
      an additional field ``type``, which contains the :ref:`LLVM<llvm-types>` or :ref:`JVM<jvm-types>`
      type to check against.

  - ``condition``: An optional condition, represented as a :ref:`Cryptol term<cryptol-json-expression>`.
    If the ``condition`` is not ``null``, then the ``pointer`` value will only point to the ``points to``
    value if the ``condition`` holds.

``argument vals``
  A list of :ref:`Crucible Setup values<setup-values>` representing the arguments to the function being verified.

``post vars``
  A list of variables in the final state section of the specification. While in many cases this
  list will be empty, it is sometimes useful to specify that functions return arbitrary values.
  These variables are represented in the same way as :ref:`above<contract-vars>`.

``post conds``
  A list of the specification's postconditions, as :ref:`Cryptol terms<cryptol-json-expression>`.

``post allocated``
  A list of allocations in the final state section of the specification. In postconditions,
  allocations specify that the function being verified allocated memory. An allocation is
  represented in the same was as :ref:`above<allocation>`.

``post points tos``
  A list of 'points-to' relationships in the final state section of the specification. These
  relationships are represented in the same was as :ref:`above<points-to>`.


``return val``
  An optional :ref:`Crucible Setup value<setup-values>` specifying the expected return value of the function being verified.

.. _proof-scripts:

Proof Scripts
=============

SAW allows one to direct a verification task using a proof script, which is simply a sequence of proof
tactics to apply. Very commonly, the proof script provided in a verification task is simply an instruction
to use an external SAT/SMT solver such as ABC, Yices, or Z3.

A proof script is represented as a JSON object with a single field:

``tactics``
  A list of proof tactics to apply to the context/goal. A proof tactic is represented as a JSON object
  containing a tag named ``tactic``, with any further fields determined by this tag. These tag values can be:

  ``use prover``
    Apply an external prover to the goal. There is an additional field
    ``prover`` which is a JSON object with a field ``name`` specifying
    what prover to use, and an optional field ``uninterpreted
    functions``. This second field is a list of names of functions taken
    as uninterpreted/abstract. The ``name`` field can be one of the following:

    * ``abc``: Default version of ABC (which may change)
    * ``boolector``: Default version of Boolector (which may change)
    * ``cvc4``: Default version of ABC (which may change); supports uninterpreted functions
    * ``internal-abc``: Linked-in version of the ABC library
    * ``mathsat``: Default version of MathSAT (which may change); supports uninterpreted functions
    * ``rme``: Internal implementation of Reed-Muller Expansion
    * ``sbv-abc``: ABC through SMT-Lib2 using the SBV library
    * ``sbv-boolector``: Boolector through SMT-Lib2 using the SBV library
    * ``sbv-cvc4``: CVC4 through SMT-Lib2 using the SBV library; supports uninterpreted functions
    * ``sbv-mathsat``: MathSAT through SMT-Lib2 using the SBV library; supports uninterpreted functions
    * ``sbv-yices``: Yices through SMT-Lib2 using the SBV library; supports uninterpreted functions
    * ``sbv-z3``: Z3 through SMT-Lib2 using the SBV library; supports uninterpreted functions
    * ``w4-abc-verilog``: ABC through Verilog using the What4 library
    * ``w4-abc-smtlib``: ABC through SMT-Lib2 using the What4 library
    * ``w4-boolector``: Boolector through SMT-Lib2 using the What4 library
    * ``w4-cvc4``: CVC4 through SMT-Lib2 using the What4 library; supports uninterpreted functions
    * ``w4-yices``: Yices through its native format using the What4 library; supports uninterpreted functions
    * ``w4-z3``: Z3 through SMT-Lib2 using the What4 library; supports uninterpreted functions
    * ``yices``: Default version of Yices (which may change); supports uninterpreted functions
    * ``z3``: Default version of Z3 (which may change); supports uninterpreted functions

  ``unfold``
    Unfold terms in the context/goal. There is an additional field ``names``, a list of the names bound on
    the server to unfold.

  ``beta reduce goal``
    Perform a single beta reduction on the proof goal.

  ``evaluate goal``
    Fully evaluate the proof goal. There is an additional field ``uninterpreted functions``, a list of names
    of functions taken as uninterpreted/abstract.

  ``simplify``
    Simplify the context/goal. There is an additional field ``rules``, a name bound to a simpset on the server.

  ``admit``
    Admit the goal as valid without checking.

  ``trivial``
    States that the goal should be trivially true (either the constant ``True`` or a function that immediately
    returns ``True``. This tactic fails if that is not the case.

.. _setup-values:

Crucible Setup Values
=====================

Setup Values encompass all values that can occur during symbolic execution, including Cryptol terms,
pointers, arrays, and structures. They are used extensively when writing the specifications provided to the
``verify`` commands. Setup Values are represented as JSON objects containing a tag field, ``setup value``,
that determines the other fields. This tag value can be:

``named``
  A term previously saved on the server. There is an additional field ``name`` giving the name bound to the
  term on the server.

``null``
  A null/empty value.

``Cryptol``
  A Cryptol term. There is an additional field ``expression`` containing a Cryptol expression.

``array``
  An array value. There is an additional field ``elements`` which is a list of :ref:`Crucible Setup values<setup-values>`
  to populate the array with.

``struct``
  A struct value. There is an additional field ``fields`` which is a list of :ref:`Crucible Setup values<setup-values>`
  to populate the struct with.

``field``
  A field of a struct. There are two additional fields:

  - ``base``: A :ref:`Crucible Setup value<setup-values>`, the structure containing the field to assign to.
  - ``field``: The name of the field to assign to.

``element lvalue``
  An element of an array. Theer are two additional fields:

  - ``base``: A :ref:`Crucible Setup value<setup-values>`, the array to be indexed for assignment.
  - ``index``: An integer giving the index into the array to be assigned to.

``global initializer``
  A constant global initializer value. There is an additional field ``name`` giving the name of the
  global variable on the server to access the initializer of.

``global lvalue``
  A global variable to be assigned to. There is an additional field ``name`` giving the name of the global
  variable on the server that is to be assigned to.

.. _llvm-types:

LLVM Types
==========

For most commands involving the introduction of variables or the allocation of space, the type of data to
be stored must be provided. Since SAW supports both LLVM and JVM verification, the types from these
respective architectures must have JSON representations. Both LLVM and JVM types are represented as JSON
objects with a tag field to indicate any additional information that must/might be present.

The tag field is named ``type``. This tag value can be:

``primitive type``
  An LLVM primitive type. This is an additional field ``primitive`` which can be any of the following:

  - ``label``: An LLVM label.
  - ``void``: The LLVM void type.
  - ``integer``: An LLVM integer. There is an additional field ``size``, an integer giving the number of
    bytes in the integer type.
  - ``float``: An LLVM float. There is an additional field ``float type`` which can be any of the following:

    + ``half``
    + ``float``
    + ``double``
    + ``fp128``
    + ``x86_fp80``
    + ``PPC_fp128``

  - ``X86mmx``: An x86 SIMD instruction.
  - ``metadata``: LLVM metadata.

``type alias``
  A type alias. There is an additional field ``alias of``, which identifies the type being aliased by name.

``array``
  An LLVM array. There are two additional fields:

  - ``size``: An integer giving the length of the array.
  - ``element type``: An :ref:`LLVM type<llvm-types>` describing the array elements.

``function``
  A function type. There are three additional fields:

  - ``return type``: An :ref:`LLVM type<llvm-types>` describing the return type of the function.
  - ``argument types``: A list of :ref:`LLVM types<llvm-types>` describing the arguments of the function.
  - ``varargs``: A Boolean indicating whether this function takes a variable number of arguments.

``pointer``
  A pointer type. There is an additional field ``to type``, an :ref:`LLVM type<llvm-types>` describing the
  referent type of the pointer.

``struct``
  A structure type. There is an additional field ``fields``, a list of :ref:`LLVM types<llvm-types>` describing
  the structure fields.

``packed struct``
  A packed structure type. There is an additional field ``fields``, a list of :ref:`LLVM types<llvm-types>` describing
  the structure fields.

``vector``
  An LLVM vector. There are two additional fields:

  - ``size``: An integer giving the length of the array.
  - ``element type``: An :ref:`LLVM type<llvm-types>` describing the array elements.

``opaque``
  An opaque structure type.

.. _jvm-types:

JVM Types
=========

As with LLVM types, there is a tag field named ``type``. This tag value can be:

``primitive type``
  A JVM primitive type. There is an additional field ``primitive`` which can be any of the following:

  - ``boolean``: A JVM Boolean.
  - ``byte``: A JVM byte.
  - ``char``: A JVM character.
  - ``double``: A JVM double-precision float.
  - ``float``: A JVM single-precsion float.
  - ``int``: A JVM integer.
  - ``long``: A JVM long integer.
  - ``short``: A JVM short integer.

``array type``
  A JVM array. There are two additional fields:

  - ``size``: An integer giving the length of the array.
  - ``element type``: An :ref:`JVM type<jvm-types>` describing the array elements.

``class type``
  A JVM class. There is an additional field ``class name`` which identifies the class.
  Class names are encoded using dots.
