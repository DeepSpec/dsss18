Set Implicit Arguments.
Set Contextual Implicit.

Require Import DeepWeb.Free.Monad.Free.

(* If we can interpret the events of one such monad as computations in
    another, we can extend that interpretation to the whole monad. *)

Definition hom
           {E1 E2 : Type -> Type}
           (f : forall X, E1 X -> M E2 X) :
  forall R, M E1 R -> M E2 R :=
  cofix hom_ R (p : M E1 R) : M E2 R :=
    match p with
    | Ret x => Ret x
    | Vis e k => bindM (f _ e) (fun x => hom_ _ (k x))
    | Tau k => Tau (hom_ _ k)
    end.

Arguments hom {E1 E2} f {R}.

Definition hom_state
           {E1 E2 : Type -> Type}
           {S : Type}
           (f : forall X, S -> E1 X -> M E2 (S * X)) :
  forall R, S -> M E1 R -> M E2 (S * R) :=
  cofix hom_ R s (p : M E1 R) : M E2 (S * R) :=
    match p with
    | Ret x => Ret (s, x)
    | Vis e k => bindM (f _ s e) (fun sa => hom_ _ (fst sa) (k (snd sa)))
    | Tau k => Tau (hom_ _ s k)
    end.

CoFixpoint hoist {E F X}
           (f : forall Z, E Z -> F Z)
           (m : M E X)
  : M F X :=
  match m with
  | Ret x => Ret x
  | Vis e k => Vis (f _ e) (fun z => hoist f (k z))
  | Tau n => Tau (hoist f n)
  end.

Definition fold_finite {E X R}
           (default : R)
           (ret_ : X -> R)
           (f : forall X, E X -> (X -> R) -> R) : nat -> M E X -> R :=
  fix fold_ max_depth t :=
    match max_depth with
    | O => default
    | S max_depth =>
      match t with
      | Ret x => ret_ x
      | Tau t => fold_ max_depth t
      | Vis e k => f _ e (fun x => fold_ max_depth (k x))
      end
    end.

(* In order to unfold a cofixpoint we have to rewrite it with [matchM]. *)
Notation idM i :=
  match i with
  | Ret x => Ret x
  | @Vis _ _ Y e k => Vis e k
  | Tau k => Tau k
  end.

Lemma matchM : forall E X (i: M E X), i = idM i.
Proof. destruct i; auto. Qed.

Arguments matchM : clear implicits.
Arguments matchM {E X}.

Lemma bind_def_core : forall E X Y s (k : X -> M E Y),
    Core.bindM s k = Core.bind_body s (fun s => Core.bindM s k) k.
Proof.
  intros.
  rewrite (matchM (Core.bindM _ _)).
  destruct s; auto.
  simpl.
  rewrite <- matchM.
  auto.
Qed.

Lemma bind_def E X Y :
  forall s (k : X -> M E Y),
    bindM s k = Core.bind_body s (fun s' => bindM s' k) (fun x => Tau (k x)).
Proof.
  unfold bindM.
  intros s k.
  rewrite bind_def_core.
  auto.
Qed.
