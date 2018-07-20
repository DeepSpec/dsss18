(** A generic specification monad, parametrized over the "co-events"
    corresponding to a "program under observation." *)

Set Implicit Arguments.
Set Contextual Implicit.
Generalizable All Variables.

From Coq Require Import
     List Equality.
Import ListNotations.

From QuickChick Require Import QuickChick.

From Custom Require Import
     String.

Require Export DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.

Import MonadNotations.
Import SumNotations.
Open Scope sum_scope.

(* TODO: Make CE a parameter of a Section for the rest. *)

Section Arbitrary.

Inductive arbitraryE : Type -> Type :=
| Arb : forall `{Show X} `{Arbitrary X}, arbitraryE X.

Arguments Arb {_ _ _ _ _}.

Class HasArbitrary (E : Type -> Type) :=
  { Arb_ : forall `{Show X} `{Arbitrary X}, E X }.

Global Instance default_HasArbitrary `{Convertible arbitraryE E}
  : HasArbitrary E :=
  { Arb_ := fun `{Show X} `{Arbitrary X} => convert Arb }.

Definition arb `{HasArbitrary E} `{Show X} `{Arbitrary X}
  : M E X :=
  liftE Arb_.

Global Instance Show_arbitraryE X : Show (arbitraryE X) :=
  { show e := "Arb" }.

End Arbitrary.

Section Alt.
(* A disjunction like [Or], but with a
   different meaning in a specification:
   - [Or]: both branches must be valid, the choice of
     the branch is determined by an external event
     (like "multiplicative disjunction" in linear logic?);
   - [Alt]: either branch can be valid, an implementation
     gets to choose ("additive disjunction"?).
   For testing, we have [Or -> conjoin], [Alt -> disjoin]. *)

Inductive altE : Type -> Type :=
| Alt : altE bool.

Class HasAlt (E : Type -> Type) :=
  { Alt_ : E bool }.

Global Instance default_HasAlt `{Convertible altE E}
  : HasAlt E :=
  { Alt_ := convert Alt }.

Definition alt `{HasAlt E} {X} (m1 m2 : M E X) : M E X :=
  Vis Alt_ (fun b : bool => if b then m1 else m2).

Global Instance Show_altE X : Show (altE X) :=
  { show e := "Alt" }.

End Alt.

Section Discard.
(* An alternative form of failure that discards a test
   case instead of failing. *)

Inductive discardE : Type -> Type :=
| Discard : string -> discardE void.

Definition discard `{Convertible discardE E} {X} (reason : string)
  : M E X :=
  Vis (convert (Discard reason)) (fun v : void => match v with end).

Global Instance Show_discardE X : Show (discardE X) :=
  { show := fun '(Discard reason) => ("Discard " ++ show reason)%string }.

End Discard.

Section Commit.

Inductive commitE : Type -> Type :=
| Commit : commitE unit.

Definition commit `{Convertible commitE E} : M E unit :=
  liftE (convert Commit).

End Commit.

Definition specE : Type -> Type :=
  commitE +' discardE +' traceE +' arbitraryE +' altE +' nondetE +' failureE.

Definition PureSpec := M specE.

(** This function zips a program and a test,
    given a function that tells
    us what to do when observable events occur. *)
Section zipM.

Variable E CE F : Type -> Type.

Variable zipE : forall {X Y}, E X -> CE Y -> M F (X * Y).

CoFixpoint zipM {A B} (p : M (F +' E) A) (t : M (F +' CE) B)
  : M F (A + B) :=
  match p, t with
    | Vis _ (| e ) pk, Vis _ (| ce ) tk =>
        p <- zipE e ce;;
        match p with (x, y) => zipM (pk x) (tk y) end
    | Tau p', _ => Tau (zipM p' t)
    | Vis _ ( e |) pk, _ => Vis e (fun x => zipM (pk x) t)
    | Ret a, _ => Ret (inl a)
    | _, Tau t' => Tau (zipM p t')
    | _, Vis _ ( e |) tk => Vis e (fun x => zipM p (tk x))
    | _, Ret b => Ret (inr b)
  end.

End zipM.
Arguments zipM {E CE F} zipE {A B}.

CoInductive valid_spec : forall A, PureSpec A -> Prop :=
| vt_tau : forall A (t : PureSpec A), valid_spec t -> valid_spec (Tau t)
| vt_trace : forall A msg tk, @valid_spec A (tk tt) -> valid_spec (Vis (convert (@Trace string _ msg)) tk)
| vt_arb : forall {A} `{Show X} `{Arbitrary X} tk,
    (forall (v : X), valid_spec (tk v)) ->
    @valid_spec A (Vis Arb_ tk)
| vt_ret : forall A x, @valid_spec A (Ret x)
| or_both : forall A tk, (forall b, @valid_spec A (tk b)) -> valid_spec (Vis (convert Or) tk)
| alt_l : forall A tk, @valid_spec A (tk true) -> valid_spec (Vis Alt_ tk)
| alt_r : forall A tk, @valid_spec A (tk false) -> valid_spec (Vis Alt_ tk).

(* TODO: Do we need c?  (It counts foralls -- it's here so that we can
   shrink the number of foralls that are considered, leading to short
   traces.  Not clear this is working well.  We wondered if QuickChick
   can be improved to shrink nested foralls alternately (as if they
   were paired), but this is fairly difficult.) *)
Fixpoint check_spec_aux {A}
         (n: nat)
         (d: nat) (* Current depth *)
         (fail_checker: Checker) (*  *)
         (t: PureSpec A)
         (c: nat)
  : Checker :=
  match n with
  | 0 => checker true
  | S n' =>
    match t with
    | Tau t' => check_spec_aux n' d fail_checker t' c
    (* Arb *)
    | Vis _ (| arb' |||) tk =>
      match arb' in arbitraryE T return (T -> _) -> _ with
      | Arb _ _ _ _ _ => fun tk =>
        match c with
        | 0 => checker true
        | S c' =>
          forAllShrinkShow arbitrary shrink (fun a => (show d ++ ": " ++ show a)%string)
                       (fun v => check_spec_aux n' (1 + d) fail_checker (tk v) c')
        end
      end tk
    (* Or *)
    | Vis _ (| or' |) tk =>
      match or' in nondetE T return (T -> _) -> _ with
      | Or => fun tk =>
                forAll arbitrary
                       (fun b => check_spec_aux n' d fail_checker (tk b) c)
      end tk
    (* Alt *)
    | Vis _ (| alt' ||) tk =>
      match alt' in altE T return (T -> _) -> _ with
      | Alt => fun tk =>
                 let fail_checker' :=
                     check_spec_aux n' d fail_checker (tk false) c
                 in
                 check_spec_aux n' d fail_checker' (tk true) c
      end tk
    (* Trace *)
    | Vis _ (| trace' ||||) tk =>
      match trace' in traceE T return (T -> _) -> _ with
      | Trace _ _ msg => fun tk =>
                       whenFail (show msg) (check_spec_aux n' d fail_checker (tk tt) c)
      end tk
    (* Discard *)
    | Vis _ (| Discard _ |||||) _ =>
      checker tt
    (* Commit *)
    | Vis _ ( commit ||||||) k =>
      match commit in commitE T return (T -> _) -> _ with
      | Commit => fun k => check_spec_aux n' d (checker false) (k tt) c
      end k
    (* Fail *)
    | Vis _ (| Fail r ) _ =>
      whenFail ("Fail " ++ show r) fail_checker
    | Ret _ => checker true
    end
  end.

Fixpoint check_spec {A} (n: nat) (t: PureSpec A) (c: nat) : Checker :=
  check_spec_aux n 0 (checker false) t c.

Fixpoint check_spec' (n: nat) (t: PureSpec unit)
         (skip : Checker)
         (fi : nat -> Checker)
         (btd : nat) (* backtrack depth *)
         (c: nat) : Checker :=
  let dec (fi : nat -> Checker) n : Checker :=
      match n with
      | O => checker false
      | S n' => fi n'
      end in
  match n with
  | 0 => whenFail "FUEL OUT" (checker true)
  | S n' =>
    match t with
    | Tau t' => check_spec' n' t' skip fi btd c

    (* Arb *)
    | Vis _ (| arb' |||) tk =>
      match arb' in arbitraryE T return (T -> _) -> _ with
      | Arb _ _ _ _ _ => fun tk =>
        match c with
        | 0 => whenFail "ARB" (checker true)
        | S c' =>
          forAllShrink arbitrary shrink
            (fun v =>
               check_spec' n' (tk v) (checker true)
                           fi btd c')
        end
      end tk

    (* Or *)
    | Vis _ (| or' |) tk =>
      match or' in nondetE T return (T -> _) -> _ with
      | Or => fun tk =>
         let skip' b := check_spec' n' (tk (negb b)) skip
                                    (dec fi) btd c in
         forAll arbitrary
                (fun b => check_spec' n' (tk b) (skip' b) (dec fi) btd c)
      end tk

    (* Alt *)
    | Vis _ (| alt' ||) tk =>
      match alt' in altE T return (T -> _) -> _ with
      | Alt => fun tk =>
        let fi' _ := whenFail "Retry"
              (check_spec' n' (tk false) (checker true) fi btd c) in
        whenFail "Save"
          (check_spec' n' (tk true) (checker true) fi' btd c)
      end tk

    (* Trace *)
    | Vis _ (| trace' ||||) tk =>
      match trace' in traceE T return (T -> _) -> _ with
      | Trace _ _ msg => fun tk =>
                       whenFail (show msg) (check_spec' n' (tk tt) skip fi btd c)
      end tk

    (* Discard *)
    | Vis _ (| Discard _ |||||) _ => checker tt

    (* Commit *)
    | Vis _ ( commit' ||||||) k =>
      match commit' in commitE T return (T -> _) -> _ with
      | Commit => fun k => check_spec' n' (k tt) skip fi btd c
      end k

    (* Fail *)
    | Vis _ (| Fail r ) _ =>
      whenFail ("Fail " ++ show r) (fi btd)

    (* Return *)
    | Ret tt => whenFail "RETURN" skip
    end
  end.

(* TODO: These are already in QC *)
Lemma semChecker_checker_true : semChecker (checker true).
Proof.
  simpl.
  rewrite semReturnGen.
  rewrite semCheckableQProp.
  reflexivity.
Qed.
Lemma semChecker_checker_false : ~ semChecker (checker false).
Proof.
  simpl.
  rewrite semReturnGen.
  rewrite semCheckableQProp.
  intro.
  inversion H.
Qed.

Section correctness.
(** This lemma looks nice. But it might not be one that can be proven,
   because of constructivity of coq? *)
Parameter semChecker_disjoin:
  forall c1 c2, semChecker (disjoin [c1; c2]) <-> semChecker c1 \/ semChecker c2.

Theorem checker_correct:
  forall A n (t : PureSpec A) l,
  valid_spec t -> semChecker (check_spec n t l).
Proof.
  induction n; intros.
  solve [apply semChecker_checker_true].
  destruct t;
(*    try (match goal with [ e: SpecE _ _ |- _ ] => destruct e; [idtac|destruct l|..] end); *)
    try solve [apply semChecker_checker_true];
    try solve [dependent destruction H; intuition];
    try solve [apply verify_tau_l in H; apply IHn; apply H];
    try solve [dependent destruction H;  simpl; try rewrite semWhenFail_id; apply IHn; apply H];
    try solve [dependent destruction H; simpl; rewrite semChecker_disjoin; (left + right); apply IHn; apply H].
Abort.
(* TODO: Fix the proof -- Trace broke it? *)

(** We can almost show completeness, as shown in the following lemma!

    The only problem is that when the test calls [or], we need to know
    whether to use [or_l] or [or_r]. But I doubt that is possible,
    because it is undecidable how much fuel we have to pass to
    [check_spec] to decide which branch to take. Bummer.  (For
    technical reasons this shows up twice, hence the two [admit]
    below. *)

Ltac absurd := match goal with
  | [ v : void |- _ ] => destruct v
  | [ v : emptyE _ |- _ ] => destruct v
  end.

Theorem checker_complete:
  forall A (t : PureSpec A),
  (forall n l, semChecker (check_spec n t l)) -> valid_spec t.
Proof.
  cofix self.
  intros.
  destruct  t.
  * auto.
  * specialize (H 2 0); auto.
  * destruct e; try absurd.
    + (* constructor; intro.
      apply checker_complete; intros. *)
Abort.
(* TODO: *)
(*       apply (H (S n) (v::l)).
    + admit.
    + specialize (H 2 []); contradict H; apply semChecker_checker_false
    + constructor; apply checker_complete; intros; apply (H (S n) l).
Abort. *)
End correctness.
