Require Export List.
Export ListNotations.

Definition null {A} (xs : list A) :=
  match xs with
  | nil => true
  | _ => false
  end.
