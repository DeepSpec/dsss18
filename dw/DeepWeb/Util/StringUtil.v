Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Basics.
Open Scope program_scope.

Require Import ExtLib.Data.List.
Require Import ExtLib.Data.String.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Programming.Injection.
Require Import ExtLib.Structures.Reducible.

From Custom Require Import
     Decidability
     Show
     String.
Open Scope string_scope.

Import MonadNotation.
Open Scope monad_scope.

Require Import DeepWeb.Util.OptionE.

(** * Miscellaneous *)
(* We don't need this for now (since we are not proving things.

Lemma substring_length : forall n size s,
    length (substring n size s) <= size.
Proof.
  intros. generalize dependent n. generalize dependent size.
  induction s; intros.
  - destruct size; destruct n; simpl; omega.
  - destruct size; induction n; simpl; try omega; eauto.
    apply le_n_S. auto.
Qed.
*)

Open Scope N_scope.

Require Import Coq.Lists.List.

Global Instance Injection_list_ascii_string : Injection (list ascii) string :=
  { inject := fold String EmptyString }.

(** The `fold` on strings are defined as `fold_left`, contrast to that
    defined on lists.  **)
Global Instance Injection_string_list_ascii : Injection string (list ascii) :=
  { inject s := rev (fold cons nil s) }.

(* ################## Parsing Backbone (from ImpParser.v) ################### *)

Definition bigNumber : nat := 3000. (* used in parsing fixpoints*)

Close Scope nat_scope.
Set Warnings "-notation-overridden,-parsing,-deprecated-implicit-arguments".
Import ListNotations.
Open Scope list_scope.

Fixpoint string_to_list_rec (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (string_to_list_rec s)
  end.

Coercion list_of_string := string_to_list_rec.

Fixpoint string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition string_of_listString (xs : list string) : string :=
  fold append "" xs.

Definition natlist_of_string (s: string) : list nat :=
  map nat_of_ascii s.

Definition stringlist_of_string : string -> list string :=
  map (fun x => String x "").

Definition string_of_natlist (xs: list nat) : string :=
  string_of_list (map ascii_of_nat xs).

Definition token := string.

(* https://tools.ietf.org/html/rfc7230#section-1.2 *)
Definition htab := ascii_of_N 9.
Definition cr := ascii_of_N 13.
Definition lf := ascii_of_N 10.
Definition crlf := String cr (String lf EmptyString).

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    (* LY: Try not to use pattern matching on ascii, it would be
    extracted to very ugly (and long) Ocaml code. *)
    if orb ((x = "(")?) ((x = ")")?) then
      tk ++ [x]::(tokenize_helper other [] xs')
    else
      match cls, classifyChar x with
      | _, white    =>
        tk ++ (tokenize_helper white [] xs')
      | alpha,alpha  =>
        tokenize_helper alpha (x::acc) xs'
      | digit,digit  =>
        tokenize_helper digit (x::acc) xs'
      | other,other  =>
        tokenize_helper other (x::acc) xs'
      | _,tp         =>
        tk ++ (tokenize_helper tp [x] xs')
      end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] s).

Example tokenize_ex1 :
    tokenize "abc12==3  223*(3+(a+c))" %string
  = ["abc"; "12"; "=="; "3"; "223";
       "*"; "("; "3"; "+"; "(";
       "a"; "+"; "c"; ")"; ")"]%string.
Proof. reflexivity. Qed.

Open Scope string.


(* Disjunction combinator notation *)
Notation "p1 |<>| p2"
  := (catch p1 (fun _ => p2))
       (right associativity, at level 60).

Section Parser.
  
Variable P : Type.
Context `{ Show P }.
Context `{ forall (a b : P), Dec (a = b) }.

Definition parser := stateT (list P) optionE.

(* A parser that parses one token *)
Definition oneStep_P : parser P :=
  xs <- get;;
  match xs with
  | [] => raise "Expected a token"
  | x::xs' => put xs';;
             ret x
  end.

(* A parser that parses one token *)
Definition peek_P : parser P :=
  xs <- get;;
  match xs with
  | [] => raise "Expected a token"
  | x::xs' => put xs;;
             ret x
  end.

(* a parser that parses one token given the condition [f] is met *)
Definition ensure_P (f: P  -> bool) : parser P :=
  x <- oneStep_P;;
    if (f x) then ret x else raise ("ensure_P did not find expected").

(* ####################### Parsing Combinators [_PC] ####################### *)

Fixpoint many_helper {T} (p : parser T) acc steps : parser (list T) :=
  match steps with
  | 0%nat => raise "Too many recursive calls"
  | S steps' =>
    (t <- p ;; many_helper p (t::acc) steps') |<>| (ret (rev acc))
  end.

(* A (step-indexed) parser that expects zero or more [p]s: *)

Fixpoint many_PC {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

(* A combinator that returns [pr] given the first token is [t] and skips it: *)
Definition firstExpect_PC  {T} (t : P) (pr : parser T) : parser T :=
  (ensure_P (fun x => (t = x)?) ;; pr)
    |<>| raise ("firstExpect_PC didn't find '" ++ (show t) ++ "'.").

(* A combinator that returns [pr] given the first token is [t] and doesn't skip  it: *)
Definition ifFirst_PC {T} (t : P) (pr : parser T) : parser T :=
  x <- peek_P ;; if (t <> x)? then raise ("ifFirst_PC didn't find '" ++ (show t) ++ "'.") else pr.

(* A parser that tries to apply disjunction between all parsers in [ps]:c *)
Definition chooseFrom_PC {T: Type} (ps: list (parser T)) : parser T :=
  fold (fun p1 acc => p1 |<>| acc) (raise "chooseFrom_PC failed") ps.

(* A parser that takes in a parser of type [S] and a function [S -> T] returning 
   a parser of type [T] *)
Definition postprocess_PC
           {S T: Type} (ps: parser S) (f: S -> T) : parser T :=
  bind ps (fun r => ret (f r)).

(* ######################### Generic Parsers [_P] ########################## *)

(* A parser that expects a particular token: *)
Definition expect_P (t : P) : parser unit :=
  firstExpect_PC t (ret tt).

(* A parser that returns a list of all tokens up until reaching [t], leaving [t] in the remaining tokens. If [t] is not found, it fails. *)
Fixpoint until_helper (steps: nat) (t: P) (acc: list P) : parser (list P) :=
  match steps with
  | 0%nat => raise "Too many recursive calls"
  | S steps' => (x <- ensure_P (fun x => (t <> x)?) ;;
                   until_helper steps' t (acc ++ [x]))
                  |<>| (ret acc)

  end.

Definition until_P (t : P) :=
  (result <- (until_helper bigNumber t []) ;;
         (peek_P ;; ret result))
  |<>| raise ("until_P failed to find '" ++ (show t) ++ "'.").

(* Same as until_P, but stops parsing until reaching a token in a list [lt]: *)
Fixpoint untilMulti_helper (steps: nat) (lt: list P) (acc: list P)
  : parser (list P) :=
  match steps with
  | 0%nat => raise "Too many recursive calls"
  | S steps' =>
    (x <- ensure_P
       (fun x => fold (fun n acc => andb ((n <> x)?) acc) true lt) ;;
                untilMulti_helper steps' lt (acc ++ [x])) |<>| (ret acc)
  end.

Definition untilMulti_P (lt: list P) : parser (list P) :=
  (result <- (untilMulti_helper bigNumber lt []) ;;
         (peek_P ;; ret result))
  |<>| raise ("untilMulti_P failed to find any of tokens from list.").

End Parser.

Arguments until_P {_} {_} {_}.
Arguments untilMulti_P {_} {_}.
Arguments parser {_}.
Arguments ensure_P {_}.
Arguments firstExpect_PC {_} {_} {_} {_}.
Arguments chooseFrom_PC {_} {_}.
Arguments expect_P {_} {_} {_}.
Arguments many_PC {_} {_}.
Arguments postprocess_PC {_} {_} {_}.

(* A parser that parses until a CRLF *)
Definition untilCRLF_P :=
  until_P "".

(* a parser that parses a token as defined by
   https://tools.ietf.org/html/rfc7230#section-3.2.6 *)
Definition token_P : parser string :=
  listrep <- untilMulti_P [""""; "("; ")"; ","; "/"; ":"; ";"; "<"; "="; ">";
                             "?"; "@"; "["; "\"; "]"; "{"; "}"] ;;
          ret (string_of_listString listrep).

(* A parser that parses a nat *)
Definition nat_P : parser nat :=
  x <- ensure_P (fun x => forallb isDigit (list_of_string x)) ;;
  ret (nat_of_string x).

Definition N_P : parser N :=
  x <- nat_P ;;
  ret (N_of_nat x).

Definition Z_P : parser Z :=
  x <- ensure_P (fun x => forallb isDigit (list_of_string x)) ;;
  (* TODO: this does not parse negative integers! *)
  ret (Z.of_nat (nat_of_string x)).

(* https://tools.ietf.org/html/rfc5234#appendix-B.1 *)
Definition WSP_P : parser unit :=
  chooseFrom_PC [
      expect_P " "%char;
      expect_P htab ].

(* A parser that expects a CRLF, followed by [p] *)
Definition firstExpectCRLF_PC {T} (pr: parser T) :=
  (firstExpect_PC "" pr) |<>| raise "firstExpectCRLF_PC failed".

(** Same as firstExpect_PC but case insensitive :*)
Definition firstExpectINS_PC {T} (t : string) (pr : parser T) : parser T :=
  (ensure_P (fun x => ((to_lower_string t) = (to_lower_string x)?)) ;; pr)
    |<>| raise ("firstExpectINS_PC didn't find '" ++ (show t) ++ "'.").

(* A 'parser' that separates a message into three parts (msg-line, headers, msg) *)
Local Open Scope list_scope.
Open Scope nat_scope.
Fixpoint init_separator_helper (l: list nat) (acc: list nat * list nat) (b: bool)
  : (list nat * list nat * list nat) :=
  match l with
  | c1 :: xs' =>
    match xs' with
    | c2 :: xs'' =>
      if andb ((c1 = 13)?) ((c2 = 10)?) (* 1st crlf*)
      then match xs'', b with
           | 13 :: 10 :: xs''', _ => (* 2nd crlf *)
             if (snd acc) = []? then (fst acc, [], xs''') (* no headers*)
             else (fst acc, snd acc ++ [13; 10], xs''') (* some headers *)
           | _, true => (* no 2nd clrf, parsed msgline *)
             init_separator_helper xs'' (fst acc, snd acc ++ [13; 10]) b
           | _, false => (* no 2nd clrf, did not parse msgline *)
             init_separator_helper xs'' (fst acc, snd acc) true
           end
      else if b then init_separator_helper xs' (fst acc, snd acc ++ [c1]) b
           else init_separator_helper xs' (fst acc ++ [c1], snd acc) b
    | _ => if b then init_separator_helper xs' (fst acc, snd acc ++ [c1]) b
           else init_separator_helper xs' (fst acc ++ [c1], snd acc) b
    end
  | [] => (fst acc, snd acc, [])
  end.

Definition init_separator (s: string) : (string * string * string) :=
  let '(a, b, c) := init_separator_helper (natlist_of_string s) ([], []) false in
  (string_of_natlist a, string_of_natlist b, string_of_natlist c).

(* A function that applies disjunction on a list of optionE values [ps]:c *)
Definition chooseFrom_optionE {T: Type} (ps: list (optionE T)) : optionE T :=
  fold (fun p1 acc => match p1 with
                      | Success v => Success v
                      | Failure _ => acc
                      end
       ) (raise "chooseFrom_optionE failed") ps.

Fixpoint postfix (s1 s2 : string) : bool :=
  match s1, s2 with
  | "", _ => true
  | _, "" => false
  | _, String h t => (s1 = s2)? || postfix s1 t
  end.
