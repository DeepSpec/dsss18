(* Instances of [QuickChick.Show]. *)

From Coq Require
     Arith NArith Fin.
Require Export QuickChick.Show.

Require Import Custom.String.

(* [Fin.t] *)
Instance Show_Fin (n : nat) : Show (Fin.t n) :=
  { show i := show (proj1_sig (Fin.to_nat i)) }.

Section NatToString. (* Also does NatFromString. *)
Import Arith.
Open Scope string_scope.
Open Scope nat_scope.

Definition digitToNat (c : ascii) : option nat :=
  let n := nat_of_ascii c in
  if andb (leb 48 n) (leb n 57) then Some (n - 48)
  else None.

Fixpoint readNatAux (s : string) (acc : nat) : option nat :=
  match s with
    | "" => Some acc
    | String c s' =>
      match digitToNat c with
        | Some n => readNatAux s' (10 * acc + n)
        | None => None
      end
  end.

Definition nat_of_string (s : string) : nat :=
  match readNatAux s 0 with
  | Some v => v
  | None => 0
  end.

(** converting a nat to a string of numbers *)

Definition natToDigit (n : nat) : ascii :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
  end.

Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (n mod 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.

Definition string_of_nat (n : nat) : string :=
  writeNatAux n n "".

End NatToString.

Section NToString.

Import NArith.

Global Instance Show_n : Show N :=
  {| show := fun n : N => string_of_nat (nat_of_N n) |}.

End NToString.

Definition pretty_char (c : ascii) : string :=
  if isPrintable c then String c ""
  else let n := N_of_ascii c in
       String "\" (if BinNat.N.ltb n 10 then "00" ++ show n
                   else if BinNat.N.ltb n 100 then String "0" (show n)
                   else show n).

Global Instance showAscii : Show ascii :=
  {| show c := ("""" ++ pretty_char c ++ """")%string |}.
