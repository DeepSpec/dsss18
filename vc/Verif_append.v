(** * Verif_append: List segments, magic wand *)

(** THIS CHAPTER IS JUST A STUB RIGHT NOW. *)

(** This chapter should show how to prove the correctness
 of adding up a list, two different ways:
 - with list-segments
 - with magic wand

 Then it should show proofs of the [append] function,
 two different ways:
 - with list-segments
 - with magic wand
*)


(* ================================================================= *)
(** ** Here is a little C program, [reverse.c] *)

(** 

#include <stddef.h>

struct list {int head; struct list *tail;};

unsigned sumlist (struct list *p) {
  unsigned s = 0;
  struct list *t = p;
  unsigned h;
  while (t) {
     h = t->head;
     t = t->tail;
     s = s + h;
  }
  return s;
}

struct list *append (struct list *x, struct list *y) {
  struct list *t, *u;
  if (x==NULL)
    return y;
  else {
    t = x;
    u = t->tail;
    while (u!=NULL) {
      t = u;
      u = t->tail;
    }
    t->tail = y;
    return x;
  }
}
*)

Require Import VST.floyd.proofauto.
Require Import append.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* ================================================================= *)
(** ** Inductive definition of linked lists *)

Definition t_list := Tstruct _list noattr.

Fixpoint listrep (sigma: list val) (p: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, 
      data_at Tsh t_list (h,y) p  *  listrep hs y
 | nil => 
    !! (p = nullval) && emp
 end.

Arguments listrep sigma p : simpl never.

(* ================================================================= *)
(** ** Hint databases for spatial operators *)

(** This is the same proof as in [Verif_reverse] *)
Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).
Proof.
intros.
revert p; induction sigma; intros p.
-
 unfold listrep.
 entailer!.
 split; auto.
-
 unfold listrep; fold listrep.
 entailer.
 entailer!.
 split; intro.
 * clear - H H2.
   subst p.
   eapply field_compatible_nullval; eauto.
 * inversion H2.
Qed.
Hint Resolve listrep_local_facts : saturate_local.

(** This is the same proof as in [Verif_reverse] *)
Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
 intros.
 unfold listrep.
 destruct sigma; simpl.
* entailer!.
* entailer!.
  auto with valid_pointer.
Qed.
Hint Resolve listrep_valid_pointer : valid_pointer.

(* ================================================================= *)
(** ** Specification of the [sumlist] and [append] functions. *)
Definition sum_int : list int -> int := fold_right Int.add Int.zero.

Definition sumlist_spec : ident * funspec :=
 DECLARE _sumlist
  WITH sigma : list int, p: val
  PRE  [ _p OF (tptr t_list) ]
     PROP ()
     LOCAL (temp _p p)
     SEP (listrep (map Vint sigma) p)
  POST [ (tptr t_list) ]
     PROP () 
     LOCAL (temp ret_temp (Vint (sum_int sigma)))
     SEP (listrep(map Vint sigma) p).

Definition append_spec :=
 DECLARE _append
  WITH sh : share, x: val, y: val, s1: list val, s2: list val
  PRE [ _x OF (tptr t_list) , _y OF (tptr t_list)]
     PROP(writable_share sh)
     LOCAL (temp _x x; temp _y y)
     SEP (listrep s1 x; listrep s2 y)
  POST [ tptr t_list ]
    EX r: val,
     PROP()
     LOCAL(temp ret_temp r)
     SEP (listrep (s1++s2) r).

Definition Gprog : funspecs :=
         ltac:(with_library prog [ sumlist_spec; append_spec ]).

(* ================================================================= *)
(** ** Proof of the [sumlist] function *)

(** TODO: Explain why we're using unsigned ints, and how
this makes the proof much easier.  Compare with the proof
 of [pop_and_add] in [Verif_triang]. *)

Lemma sum_int_app:
  forall a b, sum_int (a++b) = Int.add (sum_int a) (sum_int b).
Proof.
intros.
induction a; simpl. rewrite Int.add_zero_l; auto.
rewrite IHa. rewrite Int.add_assoc. auto.
Qed.

(** TODO: This proof needs cleanup, and lots more explanation.  **)
Lemma body_sumlist: semax_body Vprog Gprog f_sumlist sumlist_spec.
Proof.
(** Here is the standard way to start a function-body proof:  First,
 ** start-function; then forward.
 **)
start_function.
forward.  (* s = 0; *)
forward.  (* t = p; *)
forward_while
          (EX sigma2: list int, EX t: val,
            PROP ()
            LOCAL (temp _t t; temp _s (Vint (Int.sub (sum_int sigma) (sum_int sigma2))))
            SEP (listrep (map Vint sigma2) t;
                   listrep (map Vint sigma2) t -* listrep (map Vint sigma) p)).
- (* Prove that current precondition implies loop invariant *)
Exists sigma p.
entailer!.
apply wand_sepcon_adjoint. cancel.
- (* Prove that loop invariant implies typechecking condition *)
entailer!.
- (* Prove that loop body preserves invariant *)
assert_PROP (sigma2 <> nil). {
  unfold listrep at 1. entailer!. assert (t=nullval) by intuition. subst; contradiction.
}
destruct sigma2 as [ | i r]; try contradiction. clear H.
simpl map. unfold listrep at 1; fold listrep.
Intros y.
forward.
forward.
forward.
Exists (r,y).
entailer!.
f_equal.
rewrite <- Int.sub_add_l.
rewrite (Int.add_commut i).
rewrite Int.sub_shifted. auto.
apply -> wand_sepcon_adjoint.
assert (data_at Tsh t_list (Vint i, y) t * listrep (map Vint r) y |-- listrep (Vint i :: map Vint r) t).
unfold listrep at 2; fold listrep. Exists y; cancel.
sep_apply H2; clear H2.
apply modus_ponens_wand.
-
subst.
forward.
assert (map Vint sigma2 = nil) by intuition.
destruct sigma2; inv H0.
eapply derives_trans. apply modus_ponens_wand.
entailer!.
Qed.

(* ================================================================= *)
(** ** Proof of the [append] function *)

(** TODO: This proof needs cleanup, and lots more explanation.  **)
Definition lseg (s: list val) (x y : val) := 
  ALL s': list val, listrep s' y -* listrep (s ++ s') x.

Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
start_function.
forward_if.
-
 subst.
 forward.
 rewrite (proj1 H) by auto.
 unfold listrep at 1. simpl app. Exists y. entailer!.
-
  forward.
  assert_PROP (s1 <> nil). {
   unfold listrep at 1. entailer!. assert (x=nullval) by intuition. subst; contradiction.
}
destruct s1 as [ | h r]; try congruence. clear H0.
unfold listrep at 1; fold listrep.
Intros u.
forward.
clear H.
subst LOOP_BODY MORE_COMMANDS POSTCONDITION; unfold abbreviate.
apply semax_seq' with
    (EX s:list val, EX t:val, EX i:val,
      PROP (s++[i]=[h]++r)  LOCAL (temp _x x; temp _t t; temp _y y)  SEP (lseg s x t; listrep [i] t; listrep s2 y)).
forward_while (EX u:val, EX t:val, EX s': list val, EX i: val, EX r': list val,
   PROP (s' ++ [i] ++ r' = [h] ++ r)
   LOCAL (temp _u u; temp _t t; temp _x x; temp _y y)
   SEP (lseg s' x t; lseg [i] t u; listrep r' u; listrep s2 y)).
*
Exists u x (@nil val) h r. entailer.
apply sepcon_derives; auto.
apply derives_trans with (emp * (lseg [h] x u * listrep r u)).
cancel.
unfold lseg. apply allp_right; intro s'. apply wand_sepcon_adjoint.
simpl.
unfold listrep at 2; fold listrep. Exists u; cancel.
rewrite sepcon_assoc. apply sepcon_derives; auto.
unfold lseg. apply allp_right; intro s'. apply wand_sepcon_adjoint.
simpl. cancel.
*
entailer!.
*
forward.
  assert_PROP (r' <> nil). {
   entailer!. intuition.
}
destruct r' as [ | j r']; try congruence. clear H0.
unfold listrep at 1; fold listrep.
Intros z.
forward.
Exists (z,u0,s'++[i],j,r').
entailer!.
rewrite app_ass; auto.
apply sepcon_derives.
apply allp_right; intro s3.
apply -> wand_sepcon_adjoint.
unfold lseg.
allp_left (i::s3).
allp_left (s3).
sep_apply (modus_ponens_wand (listrep s3 u0) (listrep ([i]++s3) t)).
simpl.
rewrite app_ass. simpl.
apply modus_ponens_wand.
unfold lseg. apply allp_right; intro. simpl.
apply wand_sepcon_adjoint.
unfold listrep at 2; fold listrep.
Exists z. cancel.
*
subst u0.
forward.
Exists s' t i.
entailer!.
rewrite (proj1 H0 (eq_refl _)) in *.
rewrite <- app_nil_end in H; apply H.
rewrite (proj1 H0 (eq_refl _)) in *.
unfold listrep at 1. entailer!.
unfold lseg.
allp_left (@nil val).
simpl.
unfold listrep at 1. entailer!.
rewrite emp_wand. auto.
*
Intros s t i.
unfold listrep at 1.
Intros z.
subst z.
forward.
forward.
Exists x.
entailer!.
replace (h::r++s2) with (([h]++r)++s2) by (rewrite app_ass; auto).
rewrite <- H. rewrite app_ass. simpl.
apply derives_trans with (lseg s x t * listrep (i::s2) t).
unfold listrep at 2; fold listrep; Exists y; cancel.
clear.
unfold lseg. allp_left (i::s2). rewrite sepcon_comm.
apply modus_ponens_wand.
Qed.
