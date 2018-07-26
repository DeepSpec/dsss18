# Verdi Lecture 2, DeepSpec Summer School 2018


## Materials

Today we'll talk more about some verified systems and get into
"verified system transformers" which are the mechanism Verdi
modularizes fault-tolerance handling and reasoning.  We'll
walk through some solutions to yesterday's homework and then
see how real Verdi works by stepping through:

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



