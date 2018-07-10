Require Export Ascii.
Require Export String.
Require Export Arith.
Require Export Basics.

From ExtLib Require Export
     StateMonad.

From QuickChick Require Import QuickChick.

From ExtLib Require
     OptionMonad.
(* Just the instance *)

Require Export List ZArith.
Export ListNotations.

Require Export Custom.Show.

Require Export DeepWeb.Util.ListUtil.
Require Export DeepWeb.Util.StringUtil.
Require Export DeepWeb.Util.OptionE.
Require Export DeepWeb.Util.StringSynonym.

Definition sublist {A: Type} (start length : nat) (l: list A) : list A :=
  firstn length (skipn start l).

Definition app {A B : Type} (f: A->B) (a: A) : B := f a.
Notation " f $ a " := (app f a) (at level 98, left associativity).

Module PathExamples.
  Definition examples := ["/x";"/y";"/z";"/index.html"].
  Definition defaultGen := liftGen (String "/"%char ∘ show) (arbitrary : G nat).
End PathExamples.
Module Path := StringSynonym PathExamples.

Module ContentsExamples.
  Definition examples := ["foo";"bar";"baz";"foobar";"<h1>Hello World!</h1>";""].
  Definition defaultGen : G string := arbitrary.
End ContentsExamples.
Module Contents := StringSynonym ContentsExamples.

Derive Arbitrary for positive.
Derive Arbitrary for N.

(*
Parameter gettimeofday : unit -> string.
Declare ML Module "ExtractionClient".
Extract Constant gettimeofday => "ExtractionClient.time_string".

(* LYS: [timeFail] is expected to print the time of failing test case, but this
   implementation prints the ending time of all test cases. *)
Definition timeFail {prop : Type} `{Checkable prop} : prop -> Checker :=
  callback (PostFinalFailure
              Counterexample
              (fun _ _ => trace ("Failure time: " ++ gettimeofday tt ++ nl) 0)).
*)
