# Verdi Lecture 1, DeepSpec Summer School 2018

Howdy!

For this first lecture we will focus on formalization.  In particular,
we'll define "network semantics" which are at the core of Verdi.  We
will mostly be stepping through files in `SimpleDS/`.  A good order to
read through them would be:
      1. SysDef.v
      2. Fresh.v
      3. NetSem.v
      4. FreshProof.v
      5. Counter.v
      6. CounterProof.v


To explore more issues around formalization and modeling (and the
tradeoffs of working with modules in Coq), you might try:

EXERCISE 1.

  Is every invariant of system S under shuffle_step also an
  invariant under ideal_step?  Before you try to prove or
  disprove this think about how the sets of possible behaviors
  (i.e., reachable worlds) under the two semantics relate.


EXERCISE 2.

  Define a new network semantics where messages can be arbitrarily
  delayed, reordered, or duplicated.  How should systems be designed
  to tolerate these failures?


EXERCISE 3.

  Define a new network semantics where, in addition to the failures from
  the previous exercise, messages can also be dropped.

EXERCISE 4.

  Try the following extensions to our Counter system (credit all
  to James Wilcox!).

    * Extend the system with an "increment by `n`" operation.  Find a new
      state-based specification that characterizes the behavior of your
      system and prove it.

    * Extend the system with a decrement operation.  Find a new
      state-based specification that characterizes the behavior of your
      system and prove it.  What difficulties arise?

    * Extend the system with reads and prove that the specification is
      still true.

    * In a version of the system without the decrement extension, prove
      that the backup's state is always at least as large as the number of
      responses in the trace.  This rules out a buggy implementation that
      doesn't actually replicate requests.

    * Prove that the number of responses in the trace is less than or
      equal to the number of responses.  This is a completely
      trace-based/external specification!
