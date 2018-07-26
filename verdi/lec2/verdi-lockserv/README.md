Verdi LockServ
==============

[![Build Status](https://api.travis-ci.org/DistributedComponents/verdi-lockserv.svg?branch=master)](https://travis-ci.org/DistributedComponents/verdi-lockserv)

An implementation of a simple asynchronous message-passing lock server, verified to achieve mutual exclusion in the Coq proof assistant using the Verdi framework. By extracting Coq code to OCaml and linking the results to a trusted shim that handles network communication, the certified system can run on real hardware.

Requirements
------------

Definitions and proofs:

- [`Coq 8.6.1`](https://coq.inria.fr/coq-86) or [`Coq 8.7`](https://coq.inria.fr/coq-87)
- [`Verdi`](https://github.com/uwplse/verdi)
- [`StructTact`](https://github.com/uwplse/StructTact)
- [`Cheerios`](https://github.com/uwplse/cheerios)

Executable programs:

- [`OCaml 4.02.3`](https://ocaml.org) (or later)
- [`OCamlbuild`](https://github.com/ocaml/ocamlbuild)
- [`ocamlfind`](http://projects.camlcity.org/projects/findlib.html)
- [`verdi-runtime`](https://github.com/DistributedComponents/verdi-runtime)
- [`cheerios-runtime`](https://github.com/uwplse/cheerios)

Client to interface with program:

- [`Python 2.7`](https://www.python.org/download/releases/2.7/)

Testing of unverified code:

- [`OUnit 2.0.0`](http://ounit.forge.ocamlcore.org)

Building
--------

The recommended way to install the OCaml and Coq dependencies of Verdi LockServ is via [OPAM](https://coq.inria.fr/opam/www/using.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
opam install verdi StructTact cheerios verdi-runtime cheerios-runtime ocamlbuild ocamlfind
```

Then, run `./configure` in the root directory.  This will check for the appropriate version of Coq and ensure all necessary dependencies can be located.

By default, the script assumes that `Verdi`, `StructTact`, and `Cheerios` are installed in Coq's `user-contrib` directory, but this can be overridden by setting the `Verdi_PATH`, `StructTact_PATH`, and `Cheerios_PATH` environment variables.

Finally, run `make` in the root directory. This will compile the lock server definitions, check the proofs of mutual exclusion, and extract OCaml event handler code.

To build an OCaml program from the extracted code called `LockServMain.native` in the `extraction/lockserv` directory, run `make lockserv` in the root directory.

Running LockServ on a Cluster
-----------------------------

`LockServMain` accepts the following command-line options:

```
-me NAME             name for this node
-port PORT           port for inputs
-node NAME,IP:PORT   node in the cluster
-debug               run in debug mode
```

Possible node names are `Server`, `Client-0`, `Client-1`, etc.

For example, to run `LockServMain` on a cluster with IP addresses
`192.168.0.1`, `192.168.0.2`, `192.168.0.3`, input port 8000,
and port 9000 for inter-node communication, use the following:

    # on 192.168.0.1
    $ ./LockServMain.native -port 8000 -me Server -node Server,192.168.0.1:9000 \
                    -node Client-0,192.168.0.2:9000 -node Client-1,192.168.0.3:9000

    # on 192.168.0.2
    $ ./LockServMain.native -port 8000 -me Client-0 -node Server,192.168.0.1:9000 \
                    -node Client-0,192.168.0.2:9000 -node Client-1,192.168.0.3:9000

    # on 192.168.0.3
    $ ./LockServMain.native -port 8000 -me Client-1 -node Server,192.168.0.1:9000 \
                    -node Client-0,192.168.0.2:9000 -node Client-1,192.168.0.3:9000

Client Program for LockServ
---------------------------

There is a simple client written in Python in the directory `extraction/lockserv/script` that can be used as follows:

    $ python -i client.py
    >>> c=Client('192.168.0.2', 8000)
    >>> c.send_lock()
    'Locked'
    >>> c.send_unlock()

Tests for Unverified Code
-------------------------

Some example unit tests for unverified OCaml code are included in `extraction/lockserv/test`. To execute these tests, first install the OUnit library via OPAM:

```
opam install ounit
```

Then, go to `extraction/lockserv` and run `make test`.

LockServ with Sequence Numbering
--------------------------------

As originally defined, the lock server does not tolerate duplicate messages, which means that `LockServMain` can potentially give unexpected results when the underlying UDP-based runtime system generates duplicates. However, the Verdi framework defines a sequence numbering verified system transformer that when applied allows the lock server to ignore duplicate messages, while still guaranteeing mutual exclusion.

The directory `extraction/lockserv-seqnum` contains the files needed to produce an OCaml program called `LockServSeqNumMain` which uses sequence numbering. After running `./configure` in the root directory, simply run `make` in `extraction/lockserv-seqnum` to compile the program. `LockServSeqNumMain` has the same command-line options as `LockServMain`, and the Python client can be used to interface with nodes in both kinds of clusters.

LockServ with Verified Serialization
------------------------------------

The standard lock server serializes messages over the network via OCaml's `Marshal` module, which must be trusted to trust the whole system. However, using the Cheerios serialization library and a Verdi verified system transformer for Cheerios, the use of `Marshal` can be eliminated while upholding the same mutual exclusion guarantees.

The directory `extraction/lockserv-serialized` contains the files needed to produce an OCaml program called `LockServSerializedMain` which uses Cheerios and its runtime library. After running `./configure` in the root directory, simply run `make` in `extraction/lockserv-serialized` to compile the program. `LockServSerializedMain` has the same command-line options as `LockServMain`, and the Python client can be used to interface with nodes in both kinds of clusters.
