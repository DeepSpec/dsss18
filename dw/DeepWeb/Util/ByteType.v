From Custom Require Import
     Decidability
     Monad
     String.
Import MonadNotations.
Open Scope monad_scope.
Open Scope string_scope.

Definition byte : Type := ascii.
Definition bytes : Type := string.

(* Could be a more general [for_each], but [bytes] is [string],
   which is not a list. (Maybe we should stop abusing Coq's
   [string] type...). *)
Fixpoint for_each_byte {m} `{Monad m} (bs : bytes) (body : byte -> m unit)
  : m unit :=
  match bs with
  | "" => ret tt
  | String b bs' => body b;; for_each_byte bs' body
  end.
