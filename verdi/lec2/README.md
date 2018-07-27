# Verdi Lecture 2, DeepSpec Summer School 2018


## Materials

Today we'll talk more about some verified systems and get into
"verified system transformers" which are the mechanism Verdi
uses to modularize fault-tolerance handling and reasoning.  We'll
walk through some solutions to yesterday's homework and then
see how Verdi proper works by stepping through:

1. `verdi/core/HandlerMonad.v`
2. `verdi/core/Net.v`
3. `verdi/systems/Counter.v`
4. `verdi/systems/VarD.v`
5. `verdi/systems/LockServ.v`
6. `verdi/systems/PrimaryBackup.v`
7. `verdi/systems/SeqNum.v`


## Building

Verdi depends on [`mathcomp`](https://github.com/math-comp/math-comp). 
If you already have OPAM installed:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect
```

For other ways of getting `mathcomp` installed, see their [install
docs](https://github.com/math-comp/math-comp/blob/master/INSTALL.md).

Once dependencies have been installed, you should be able to build
everything by running `make` in this directory:

```
make
```


## Exercises

1. See the exercises and mini-project in `SimpleDS/SeqNumProof.v`.
   The suggested exercises will require coming up with your own
   inductive invariants -- the hard part of any systems verification!

2. Write the analog of our Fresh system from SimpleDS (SimpleDS/Fresh.v)
   but in Verdi.  Look at the various semantics Verdi provides and
   select the most appropriate one (verdi/core/Net.v).  How does
   writing a system using type classes differ from writing one
   based on modules / functors?  Now prove your Verdi version of
   the Fresh system correct.  Is your spec or proof different from
   what we did in SimpleDS?

3. Try doing the "Counter" exercises from the previous lecture
   (see ../lec1), but in Verdi instead of SimpleDS (i.e., based on
   `verdi/systems/Counter.v`).

4. Use Verdi's SeqNum system transformer to construct a version of
   Counter that tolerates message duplication.

5. We're spending all this effort to prove stuff about distributed
   systems, but how do they actually run?  Follow the instructions
   in `verdi-lockserv/README.md` to build an executable version
   of the Verdi lock server and run it.  Use `-debug` to get a
   better feel for what the system is doing.

   (Note 1: the easiest way to do this is to run the server and
   clients all on your machine locally (127.0.0.1) and use a
   different port for each node.)

   (Note 2: You are strongly encouraged to install the
   Cheerios and Verdi runtime via OPAM rather than trying to
   compile the copies of those repos included in this directory.
   This is the method suggested in the verdi-lockserv README,
   so if you just follow that, everything "should be just fine.")

6. Our executable lock server depends on unverified shim code
   written in OCaml.  You can see what the code looks like by
   browsing through the `verdi-runtime` directory which contains
   all the shim code we use for Verdi.  There's a lot more in
   there just "send()" and "recv()" for packets!  How should
   we convince ourselves shims like these are correct?  What
   would be required for a bug in the Verdi shim to actually
   cause a theorem we proved in Coq to not hold?

