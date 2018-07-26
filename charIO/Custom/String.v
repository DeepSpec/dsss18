(* String utilities. *)

From Coq Require
     Bool List NArith.
Import List.ListNotations.

From Coq Require Export
     String Ascii.

From QuickChick Require Import QuickChick.

Infix ":::" := String (at level 60, right associativity) : string_scope.

Definition ascii_eq (l r : Ascii.ascii) : bool :=
  match l , r with
    | Ascii.Ascii l1 l2 l3 l4 l5 l6 l7 l8 ,
      Ascii.Ascii r1 r2 r3 r4 r5 r6 r7 r8 =>
      Bool.eqb l1 r1 &&
      Bool.eqb l2 r2 &&
      Bool.eqb l3 r3 &&
      Bool.eqb l4 r4 &&
      Bool.eqb l5 r5 &&
      Bool.eqb l6 r6 &&
      Bool.eqb l7 r7 &&
      Bool.eqb l8 r8
  end%bool.

Fixpoint string_eq (l r : string) : bool :=
  match l, r with
  | "", "" => true
  | String l0 ls, String r0 rs =>
    ascii_eq l0 r0 && string_eq ls rs
  | _, _ => false
  end.

Lemma ascii_eq_refl: forall a, ascii_eq a a = true.
Proof. intros [[] [] [] [] [] [] [] []]; auto. Qed.

Lemma string_eq_refl: forall s, string_eq s s = true.
Proof.
  intros.
  induction s.
  * auto.
  * simpl.
    rewrite IHs.
    rewrite ascii_eq_refl.
    auto.
Qed.

Section CharClass.
Import NArith.
Open Scope N_scope.

Definition isWhite (c : ascii) : bool :=
  let n := N_of_ascii c in
  orb (orb (N.eqb n 32)   (* space *)
           (N.eqb n 9))   (* tab *)
      (orb (N.eqb n 10)   (* linefeed *)
           (N.eqb n 13)). (* Carriage return. *)

Definition isLowerAlpha (c : ascii) : bool :=
  let n := N_of_ascii c in
    andb (97 <=? n) (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
  let n := N_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c : ascii) : bool :=
  let n := N_of_ascii c in
     andb (48 <=? n) (n <=? 57).

Definition isPrintable (c : ascii) : bool :=
  let n := N_of_ascii c in
  andb (32 <=? n) (n <? 127).

Inductive chartype := white | alpha | digit | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else
    other.

Definition is_lower (c: ascii) : bool :=
  let n := N_of_ascii c in
  (97 <=? n) && (n <=? 122).

Definition is_upper (c: ascii) : bool :=
  let n := N_of_ascii c in
  (65 <=? n) && (n <=? 90).

Definition to_lower (c: ascii) : ascii :=
  if is_upper c then
    ascii_of_N ((N_of_ascii c) + 32)
  else c.

Definition to_upper (c: ascii) : ascii :=
  if is_lower c then
    ascii_of_N ((N_of_ascii c) - 32)
  else c.

End CharClass.

Definition map_string (f : ascii -> ascii) : string -> string :=
  fix map_f s :=
    match s with
    | "" => ""
    | String c s' => String (f c) (map_f s')
    end.

Definition to_lower_string (s : string) : string :=
  map_string to_lower s.

Fixpoint reverse_string' (s s' : string) : string :=
  match s with
  | EmptyString => s'
  | String c s => reverse_string' s (String c s')
  end.

Definition reverse_string (s : string) : string :=
  reverse_string' s EmptyString.

Fixpoint repeat_string (c : ascii) (n : nat) :=
  match n with
  | O => ""
  | S n => String c (repeat_string c n)
  end.

Lemma repeat_string_length:
  forall c n,
    String.length (repeat_string c n) = n.
Proof.
  induction n; auto.
  simpl.
  f_equal.
  assumption.
Qed.

(* Use n here as the ranking function to show that this terminates.
   Use (length l) should be enough. *)
Fixpoint bits_to_string (n: nat) (l: list bool) (s : string) : string :=
  match n with
  | O => s
  | S n' =>
    match l with
    | nil => reverse_string s
    | l => bits_to_string n' (List.skipn 8 l)
                         (String (ascii_of_N (N_of_digits (List.rev (List.firstn 8 l)))) s)
    end
  end.

Definition list_bits_to_string (l: list (list bool)) : string :=
  let l' := List.concat l in
  bits_to_string (List.length l') l' EmptyString.

(* More lemmas *)

Lemma append_nil :
  forall s, (s ++ "")%string = s.
Proof.
  induction s.
  - auto.
  - simpl; rewrite IHs; auto.
Qed.

Lemma append_assoc :
  forall s s' s'', ((s ++ s') ++ s'' = s ++ (s' ++ s''))%string.
Proof.
  induction s.
  - auto.
  - intros; simpl; rewrite IHs; auto.
Qed.

Lemma append_byte_assoc :
  forall s b s', ((s ++ String b "") ++ s' = s ++ String b s')%string.
Proof.
  intros.
  apply append_assoc.
Qed.


(* ---------------------- *)
(* Ascii and string typeclass instances *)

Instance gSizedAscii : GenSized ascii :=
  {| arbitrarySized := fun _ => liftGen ascii_of_nat (choose (0,127)) |}.
Derive GenSized for string.

Global Instance shrinkAscii : Shrink ascii :=
  {| shrink c :=
       if (c = "a"%char)? then []
       else if (c = "b"%char)? then ["a"%char]
       else ["a"%char;"b"%char]
  |}%list.

Fixpoint shrinkStringAux (s:string) :=
  match s with
  | "" => nil
  | c ::: cs =>
    (  [cs]
    ++ List.map (fun c' => String c' cs) (shrink c)
    ++ List.map (fun cs' => String c cs') (shrinkStringAux cs))%list
  end.

Global Instance shrinkString : Shrink string :=
  {| shrink := shrinkStringAux |}.
