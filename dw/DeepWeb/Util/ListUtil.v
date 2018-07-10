From QuickChick Require Import QuickChick.
Require Import Coq.Lists.List.
Require Import String.
Import ListNotations.

Fixpoint range_rec l r : list nat :=
  match Nat.leb l r with
  | true => match r with
           | S r' => r :: range_rec l r'
           | O => 0 :: nil
           end
  | false => nil
  end.

Definition range l r: list nat :=
  rev (range_rec l r).

Fixpoint list_contents (l : list string) : string :=
  match l with
    | [] => ""
    | [h] => h
    | h::t => h ++ nl ++
             "---------------------" ++
             nl ++ list_contents t
  end.
