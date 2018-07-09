(* A monad isomorphic to [option], but we redefine it to avoid
   universe inconsistencies due to [option] being used with all
   kinds of big types already. *)

From Custom Require Import Monad.

Inductive maybe (a : Type) : Type :=
| Just : a -> maybe a
| Nothing : maybe a
.

Arguments Just {a}.
Arguments Nothing {a}.

Instance Monad_maybe : Monad maybe :=
  { ret := @Just;
    bind := fun _ _ oa k =>
              match oa with
              | Just a => k a
              | Nothing => Nothing
              end;
  }.
