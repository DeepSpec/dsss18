# Verdi Lecture 3, DeepSpec Summer School 2018


## Materials

For our last lecture together, we'll take a high-level tour of
the Verdi Raft development, discuss some of the ideas about how
to manage proof engineering for large projects, challenges around
TCBs and shims, and some potential directions folks might
explore to tackle more challenges in distributed systems.  These
files follow the key points from the slides:

1. `verdi-raft/raft/Raft.v`
2. `verdi-raft/raft/Linearizability.v`
3. `verdi-raft/raft-proofs/EndToEndLinearizability.v`
4. `verdi-raft/raft/StateMachineSafetyInterface.v`
5. `verdi/core/GhostSimulations.v`
6. `verdi/systems/LiveLockServ.v`
7. `verdi-raft/proofalytics/proof-sizes.awk`
8. `verdi/systems/SerializedMsgParams.v`


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
make -j 3 raft
```

Building Verdi Raft on one core takes about one hour.

