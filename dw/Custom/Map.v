(* Total maps *)

(* This module is meant to be [Require]-d but not [Import]-ed. *)

From QuickChick Require Import Decidability.

Section Map.

Variable K V : Type.
Context `{Eq K}.

Definition t : Type := K -> V.

Definition update : K -> V -> t -> t :=
  fun k0 v0 f k => if k = k0 ? then v0 else f k.

Definition lookup : t -> K -> V := fun f => f.

Lemma update_lookup_eq k k' v m :
  k = k' ->
  lookup (update k v m) k' = v.
Proof.
  intro Hk.
  unfold lookup.
  unfold update.
  destruct dec.
  - auto.
  - subst; contradiction.
Qed.

Lemma update_lookup_neq k k' v m :
  k <> k' ->
  lookup (update k v m) k' = lookup m k'.
Proof.
  intros Hk.
  unfold lookup.
  unfold update.
  destruct dec.
  - subst; contradiction.
  - auto.
Qed.

Lemma update_update_eq k k' v v' m :
  k = k' ->
  update k v (update k' v' m) = update k v m.
Proof.
(* Extensionally... *)
Admitted.

Lemma lookup_update_eq k k' v m :
  k = k' ->
  v = lookup m k' ->
  update k v m = m.
Proof.
(* Also extensional... *)
Admitted.

End Map.

Arguments t K V : assert.
Arguments update {K V _}.
Arguments lookup {K V}.
