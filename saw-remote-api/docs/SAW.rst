SAW RPC Server
==============

Fundamental Protocol
--------------------

This application is a `JSON-RPC <https://www.jsonrpc.org/specification>`_ server. Additionally, it maintains a persistent cache of application states and explicitly indicates the state in which each command is to be carried out.

Transport
~~~~~~~~~

The server supports three transport methods:


``stdio``
  in which the server communicates over ``stdin`` and ``stdout``
  
  

Socket
  in which the server communicates over ``stdin`` and ``stdout``
  
  

HTTP
  in which the server communicates over HTTP
  
  
In both ``stdio`` and socket mode, messages are delimited using `netstrings. <http://cr.yp.to/proto/netstrings.txt>`_


Application State
~~~~~~~~~~~~~~~~~

According to the JSON-RPC specification, the ``params`` field in a message object must be an array or object. In this protocol, it is always an object. While each message may specify its own arguments, every message has a parameter field named ``state``.

When the first message is sent from the client to the server, the ``state`` parameter should be initialized to the JSON null value ``null``. Replies from the server may contain a new state that should be used in subsequent requests, so that state changes executed by the request are visible. Prior versions of this protocol represented the initial state as the empty array ``[]``, but this is now deprecated and will be removed.

In particular, per JSON-RPC, non-error replies are always a JSON object that contains a ``result`` field. The result field always contains an ``answer`` field and a ``state`` field, as well as ``stdout`` and ``stderr``.


``answer``
  The value returned as a response to the request (the precise contents depend on which request was sent)
  
  

``state``
  The state, to be sent in subsequent requests. If the server did not modify its state in response to the command, then this state may be the same as the one sent by the client.
  
  

``stdout`` and ``stderr``
  These fields contain the contents of the Unix ``stdout`` and ``stderr`` file descriptors. They are intended as a stopgap measure for clients who are still in the process of obtaining structured information from the libraries on which they depend, so that information is not completely lost to users. However, the server may or may not cache this information and resend it. Applications are encouraged to used structured data and send it deliberately as the answer.
  
  
The precise structure of states is considered an implementation detail that could change at any time. Please treat them as opaque tokens that may be saved and re-used within a given server process, but not created by the client directly.



Summary
-------

A remote server for `SAW <https://saw.galois.com/>`_ for verifying programs with a featureset similar to SAWScript.


Methods
-------

SAW RPC Server (command)
~~~~~~~~~~~~~~~~~~~~~~~~


``module name``
  Name of module to load.
  
  
Load the specified Cryptol module.


SAW RPC Server (command)
~~~~~~~~~~~~~~~~~~~~~~~~


``file``
  File to load as a Cryptol module.
  
  
Load the given file as a Cryptol module.


SAW RPC Server (command)
~~~~~~~~~~~~~~~~~~~~~~~~


``name``
  The name to assign to the expression for later reference.
  
  

``expression``
  The expression to save.
  
  
Save a term to be referenced later by name.


SAW RPC Server (command)
~~~~~~~~~~~~~~~~~~~~~~~~


``name``
  The name to refer to the loaded module by later.
  
  

``bitcode file``
  The file containing the bitcode LLVM module to load.
  
  
Load the specified LLVM module.


SAW RPC Server (command)
~~~~~~~~~~~~~~~~~~~~~~~~


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
  
  
Verify the named LLVM function meets its specification.


SAW RPC Server (command)
~~~~~~~~~~~~~~~~~~~~~~~~


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
  
  
Verify an x86 function from an ELF file for use as an override in an LLVM verification meets its specification.


SAW RPC Server (command)
~~~~~~~~~~~~~~~~~~~~~~~~


``module``
  The LLVM  module containing the function.
  
  

``function``
  The function we are assuming a contract for.
  
  

``contract``
  The specification to assume for the function.
  
  

``lemma name``
  The name to refer to this assumed contract by later.
  
  
Assume the function meets its specification.


SAW RPC Server (command)
~~~~~~~~~~~~~~~~~~~~~~~~


``elements``
  The items to include in the simpset.
  
  

``result``
  The name to assign to this simpset.
  
  
Create a simplification rule set from the given rules.


SAW RPC Server (command)
~~~~~~~~~~~~~~~~~~~~~~~~


``script``
  Script to use to prove the term.
  
  

``term``
  The term to interpret as a theorm and prove.
  
  
Attempt to prove the given term representing a theorem, given a proof script context.


SAW RPC Server (command)
~~~~~~~~~~~~~~~~~~~~~~~~


``option``
  The option to set and its accompanying value (i.e., true or false); one of the following:``lax arithmetic``, ``SMT array memory model``, or ``What4 hash consing``
  
  
Set a SAW option in the server.


SAW RPC Server (notification)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


``state to clear``
  The state to clear from the server to make room for other unrelated states.
  
  
Clear a particular state from the SAW server (making room for subsequent/unrelated states).


SAW RPC Server (notification)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No parameters

Clear all states from the SAW server (making room for subsequent/unrelated states).





