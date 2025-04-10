SAW RPC Server
==============

Fundamental Protocol
--------------------

This application is a `JSON-RPC <https://www.jsonrpc.org/specification>`_ server. Additionally, it maintains a persistent cache of application states and explicitly indicates the state in which each command is to be carried out.

Transport
~~~~~~~~~

The server supports three transport methods:


``stdio``
  in which the server communicates over ``stdin`` and ``stdout`` using `netstrings. <http://cr.yp.to/proto/netstrings.txt>`_
  
  

``socket``
  in which the server communicates over a socket using `netstrings. <http://cr.yp.to/proto/netstrings.txt>`_
  
  

``http``
  in which the server communicates over a socket using HTTP.
  
  

Application State
~~~~~~~~~~~~~~~~~

According to the JSON-RPC specification, the ``params`` field in a message object must be an array or object. In this protocol, it is always an object. While each message may specify its own arguments, every message has a parameter field named ``state``.

When the first message is sent from the client to the server, the ``state`` parameter should be initialized to the JSON null value ``null``. Replies from the server may contain a new state that should be used in subsequent requests, so that state changes executed by the request are visible.

In particular, per JSON-RPC, non-error replies are always a JSON object that contains a ``result`` field. The result field always contains an ``answer`` field and a ``state`` field, as well as ``stdout`` and ``stderr``.


``answer``
  The value returned as a response to the request (the precise contents depend on which request was sent).
  
  

``state``
  The state, to be sent in subsequent requests. If the server did not modify its state in response to the command, then this state may be the same as the one sent by the client. When a new state is in a server response, the previous state may no longer be available for requests.
  
  

``stdout`` and ``stderr``
  These fields contain the contents of the Unix ``stdout`` and ``stderr`` file descriptors. They are intended as a stopgap measure for clients who are still in the process of obtaining structured information from the libraries on which they depend, so that information is not completely lost to users. However, the server may or may not cache this information and resend it. Applications are encouraged to used structured data and send it deliberately as the answer.
  
  
The precise structure of states is considered an implementation detail that could change at any time. Please treat them as opaque tokens that may be saved and re-used within a given server process, but not created by the client directly.



Summary
-------

A remote server for `SAW <https://saw.galois.com/>`_ for verifying programs with a featureset similar to SAWScript.


Methods
-------

SAW/Cryptol/load module (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Load the specified Cryptol module.

Parameter fields
++++++++++++++++


``module name``
  Name of module to load.
  
  

Return fields
+++++++++++++

No return fields



SAW/Cryptol/load file (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Load the given file as a Cryptol module.

Parameter fields
++++++++++++++++


``file``
  File to load as a Cryptol module.
  
  

Return fields
+++++++++++++

No return fields



SAW/Cryptol/save term (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Save a term to be referenced later by name.

Parameter fields
++++++++++++++++


``name``
  The name to assign to the expression for later reference.
  
  

``expression``
  The expression to save.
  
  

Return fields
+++++++++++++

No return fields



SAW/JVM/load class (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Load the JVM class with the given name for later verification.

Parameter fields
++++++++++++++++


``name``
  The name of the class on the server.
  
  

``class name``
  The java class to load.
  
  

Return fields
+++++++++++++

No return fields



SAW/JVM/verify (command)
~~~~~~~~~~~~~~~~~~~~~~~~

Verify the named JVM method meets its specification.

Parameter fields
++++++++++++++++


``module``
  The module of the function being verified.
  
  

``function``
  The function being verified.
  
  

``lemmas``
  The specifications to use for other functions during this verification.
  
  

``check sat``
  Whether or not to enable path satisfiability checking.
  
  

``contract``
  The specification to verify for the function.
  
  

``script``
  The script to use to prove the validity of the resulting verification conditions.
  
  

``lemma name``
  The name to refer to this verification/contract by later.
  
  

Return fields
+++++++++++++

No return fields



SAW/JVM/assume (command)
~~~~~~~~~~~~~~~~~~~~~~~~

Assume the named JVM method meets its specification.

Parameter fields
++++++++++++++++


``module``
  The LLVM  module containing the function.
  
  

``function``
  The function we are assuming a contract for.
  
  

``contract``
  The specification to assume for the function.
  
  

``lemma name``
  The name to refer to this assumed contract by later.
  
  

Return fields
+++++++++++++

No return fields



SAW/LLVM/load module (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Load the specified LLVM module.

Parameter fields
++++++++++++++++


``name``
  The name to refer to the loaded module by later.
  
  

``bitcode file``
  The file containing the bitcode LLVM module to load.
  
  

Return fields
+++++++++++++

No return fields



SAW/LLVM/verify (command)
~~~~~~~~~~~~~~~~~~~~~~~~~

Verify the named LLVM function meets its specification.

Parameter fields
++++++++++++++++


``module``
  The module of the function being verified.
  
  

``function``
  The function being verified.
  
  

``lemmas``
  The specifications to use for other functions during this verification.
  
  

``check sat``
  Whether or not to enable path satisfiability checking.
  
  

``contract``
  The specification to verify for the function.
  
  

``script``
  The script to use to prove the validity of the resulting verification conditions.
  
  

``lemma name``
  The name to refer to this verification/contract by later.
  
  

Return fields
+++++++++++++

No return fields



SAW/LLVM/verify x86 (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Verify an x86 function from an ELF file for use as an override in an LLVM verification meets its specification.

Parameter fields
++++++++++++++++


``module``
  The LLVM  module of the caller.
  
  

``object file``
  The ELF file containing the function to be verified.
  
  

``function``
  The function to be verified's symbol name.
  
  

``globals``
  The names and sizes (in bytes) of global variables to initialize.
  
  

``lemmas``
  The specifications to use for other functions during this verification.
  
  

``check sat``
  Whether or not to enable path satisfiability checking.
  
  

``contract``
  The specification to verify for the function.
  
  

``script``
  The script to use to prove the validity of the resulting verification conditions.
  
  

``lemma name``
  The name to refer to this verification/contract by later.
  
  

Return fields
+++++++++++++

No return fields



SAW/LLVM/assume (command)
~~~~~~~~~~~~~~~~~~~~~~~~~

Assume the function meets its specification.

Parameter fields
++++++++++++++++


``module``
  The LLVM  module containing the function.
  
  

``function``
  The function we are assuming a contract for.
  
  

``contract``
  The specification to assume for the function.
  
  

``lemma name``
  The name to refer to this assumed contract by later.
  
  

Return fields
+++++++++++++

No return fields



SAW/MIR/load module (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Load the specified MIR module.

Parameter fields
++++++++++++++++


``name``
  The name to refer to the loaded module by later.
  
  

``JSON file``
  The file containing the MIR JSON file to load.
  
  

Return fields
+++++++++++++

No return fields



SAW/MIR/verify (command)
~~~~~~~~~~~~~~~~~~~~~~~~

Verify the named MIR method meets its specification.

Parameter fields
++++++++++++++++


``module``
  The module of the function being verified.
  
  

``function``
  The function being verified.
  
  

``lemmas``
  The specifications to use for other functions during this verification.
  
  

``check sat``
  Whether or not to enable path satisfiability checking.
  
  

``contract``
  The specification to verify for the function.
  
  

``script``
  The script to use to prove the validity of the resulting verification conditions.
  
  

``lemma name``
  The name to refer to this verification/contract by later.
  
  

Return fields
+++++++++++++

No return fields



SAW/MIR/assume (command)
~~~~~~~~~~~~~~~~~~~~~~~~

Assume the named MIR method meets its specification.

Parameter fields
++++++++++++++++


``module``
  The LLVM  module containing the function.
  
  

``function``
  The function we are assuming a contract for.
  
  

``contract``
  The specification to assume for the function.
  
  

``lemma name``
  The name to refer to this assumed contract by later.
  
  

Return fields
+++++++++++++

No return fields



SAW/MIR/find ADT (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~

Consult the a MIR module to find an algebraic data type (ADT) with the supplied identifier and type parameter substitutions. If such an ADT cannot be found in the module, this will raise an error.

Parameter fields
++++++++++++++++


``module``
  The server name of the MIR module containing the ADT.
  
  

``ADT original name``
  The original (pre-monomorphized) ADT name.
  
  

``type substitutions``
  The types to substitute the ADT's type parameters with.
  
  

``ADT server name``
  The server name to refer to the ADT by later.
  
  

Return fields
+++++++++++++

No return fields



SAW/Yosys/import (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~

Import a file produced by the Yosys "write_json" command

Parameter fields
++++++++++++++++


``name``
  The name to refer to the record of Yosys modules by later.
  
  

``path``
  The path to the Yosys JSON file to import.
  
  

Return fields
+++++++++++++

No return fields



SAW/Yosys/verify (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~

Verify that the named HDL module meets its specification

Parameter fields
++++++++++++++++


``import``
  The imported Yosys file.
  
  

``module``
  The HDL module to verify.
  
  

``preconds``
  Any preconditions for the verificatiion.
  
  

``spec``
  The specification to verify for the module.
  
  

``lemmas``
  The lemmas to use for other modules during this verification.
  
  

``script``
  The script to use to prove the validity of the resulting verification conditions.
  
  

``lemma name``
  The name to refer to the result by later.
  
  

Return fields
+++++++++++++

No return fields



SAW/Yosys/import sequential (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Import a sequential circuit from a file produced by the Yosys "write_json" command

Parameter fields
++++++++++++++++


``name``
  The name to refer to the record of Yosys modules by later.
  
  

``path``
  The path to the Yosys JSON file to import.
  
  

``module``
  The sequential module within the Yosys JSON file to analyze.
  
  

Return fields
+++++++++++++

No return fields



SAW/Yosys/extract sequential (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Extract a term from a sequential circuit

Parameter fields
++++++++++++++++


``name``
  The name to refer extracted term by later.
  
  

``cycles``
  The number of cycles over which to iterate the term.
  
  

``module``
  The name of the sequential module to analyze.
  
  

Return fields
+++++++++++++

No return fields



SAW/create ghost variable (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Create a ghost global variable to represent proof-specific program state.

Parameter fields
++++++++++++++++


``display name``
  The name to assign to the ghost variable for display.
  
  

``server name``
  The server name to use to access the ghost variable later.
  
  

Return fields
+++++++++++++

No return fields



SAW/make simpset (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~

Create a simplification rule set from the given rules.

Parameter fields
++++++++++++++++


``elements``
  The items to include in the simpset.
  
  

``result``
  The name to assign to this simpset.
  
  

Return fields
+++++++++++++

No return fields



SAW/prove (command)
~~~~~~~~~~~~~~~~~~~

Attempt to prove the given term representing a theorem, given a proof script context.

Parameter fields
++++++++++++++++


``script``
  Script to use to prove the term.
  
  

``goal``
  The goal to interpret as a theorm and prove.
  
  

Return fields
+++++++++++++


``status``
  A string (one of ``valid````, ````invalid``, or ``unknown``) indicating whether the proof went through successfully or not.
  
  

``counterexample``
  Only used if the ``status`` is ``invalid``. An array of objects where each object has a ``name`` string and a :ref:`JSON Cryptol expression <Expression>` ``value``.
  
  


SAW/eval int (command)
~~~~~~~~~~~~~~~~~~~~~~

Attempt to evaluate the given term to a concrete integer.

Parameter fields
++++++++++++++++


``expr``
  The Cryptol expression to evaluate.
  
  

Return fields
+++++++++++++


``value``
  The integer value of the expresssion.
  
  


SAW/eval bool (command)
~~~~~~~~~~~~~~~~~~~~~~~

Attempt to evaluate the given term to a concrete boolean.

Parameter fields
++++++++++++++++


``expr``
  The Cryptol expression to evaluate.
  
  

Return fields
+++++++++++++


``value``
  The boolean value of the expresssion.
  
  


SAW/set option (command)
~~~~~~~~~~~~~~~~~~~~~~~~

Set a SAW option in the server.

Parameter fields
++++++++++++++++


``option``
  The option to set and its accompanying value (i.e., true or false); one of the following:``lax arithmetic``, ``lax pointer ordering``, ``lax loads and stores``, ``debug intrinsics``, ``SMT array memory model``, ``What4 hash consing``, or ``What4 eval``
  
  

Return fields
+++++++++++++

No return fields



SAW/clear state (notification)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Clear a particular state from the SAW server (making room for subsequent/unrelated states).

Parameter fields
++++++++++++++++


``state to clear``
  The state to clear from the server to make room for other unrelated states.
  
  

Return fields
+++++++++++++

No return fields



SAW/clear all states (notification)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Clear all states from the SAW server (making room for subsequent/unrelated states).

Parameter fields
++++++++++++++++

No parameters


Return fields
+++++++++++++

No return fields






