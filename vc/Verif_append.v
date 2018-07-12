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

(** In separation-logic assertions, how should one specify integer values?
    Normally, one should use the mathematical integers, Coq's [Z] type.
    Then, inject [Z] into the 32-bit machine integers using Int.repr,
    then from those into CompCert values by Vint.  That is,
    [Vint (Int.repr z)], where [z:Z] is a mathematical integer.

    If [z] is too big to fit in a 32-bit integer, [Int.repr] will take
    the low-order 32 bits (i.e., modulo 2^32).  To make sure that doesn't
    happen (if you didn't intend it), usually you maintain the assertion
    [Int.min_signed <= z <= Int.max_signed].  

    In this program, we are adding up a list of integers.  If we wanted
    to prove that every partial sum is in range, we'd need a complicated
    precondition.  Instead, we'll prove something simpler:  that the
    sum mod 2^32 is right.   

    In the C language, signed integer arithmetic is not allowed to
    overflow (you get undefined behavior), so we must write this program
    to use unsigned ints.  For that, we want to reason about
    32-bit machine integers directly, not about the mathematical integers.
    Therefore we'll use values of type [int], that is [Int.int], the
    type of 32-bit machine integers.  That's why, in [sumlist_spec],
    we use [sigma: list int] in our specification, instead of a list of [Z].

    Compare with the proof of [pop_and_add] in [Verif_triang],
    where we _do_ prove that each partial sum doesn't overflow, and
    we can use signed integer arithmetic. *)

(* ================================================================= *)
(** ** Proof of the [sumlist] function *)

(** First, we prove a useful auxiliary lemma about [sum_int] *)

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
(** Here is the standard way to start a function-body proof:  
    First, [start-function], then [forward]. **)
start_function.
forward.  (* s = 0; *)
forward.  (* t = p; *)
forward_while
    (EX sigma2: list int, EX t: val,
     PROP ()
     LOCAL (temp _t t;
            temp _s (Vint (Int.sub (sum_int sigma) (sum_int sigma2))))
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
  unfold listrep at 1. 
  entailer!. 
  assert (t=nullval) by intuition. 
  subst; contradiction.
}
destruct sigma2 as [ | i r]; try contradiction.
clear H.
simpl map.
unfold listrep at 1; fold listrep.
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
assert (data_at Tsh t_list (Vint i, y) t * listrep (map Vint r) y 
         |-- listrep (Vint i :: map Vint r) t).
unfold listrep at 2; fold listrep. 
Exists y; cancel.
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

Lemma lseg_nullval: forall s t, lseg s t nullval = listrep s t.
Proof.  
unfold lseg; intros.
apply pred_ext.
apply allp_left with (@nil val).
unfold listrep at 1.
rewrite prop_true_andp by auto.
rewrite emp_wand.
rewrite <- app_nil_end.
auto.
apply allp_right; intro s'.
apply wand_sepcon_adjoint.
unfold listrep at 2.
destruct s'; simpl.
rewrite <- app_nil_end. entailer!.
Intros y.
entailer!.
destruct H0; contradiction H0.
Qed.

Lemma lseg_listrep: forall s t x y ,
      lseg s x y * listrep t y |-- listrep (s++t) x.
Proof.
intros.
unfold lseg.
allp_left t.
rewrite sepcon_comm.
apply modus_ponens_wand.
Qed.

Lemma lseg_app:
   forall s t x y z,
      lseg s x y * lseg t y z |-- lseg (s++t) x z.
Proof.
  intros.
 apply allp_right; intro u.
 apply -> wand_sepcon_adjoint.
 sep_apply (lseg_listrep t u y z).
 sep_apply (lseg_listrep s (t++u) x y).
 rewrite app_ass.
 auto.
Qed.
  
Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
start_function.
forward_if.
{ (* then-clause *)
 subst.
 forward.
 rewrite (proj1 H) by auto.
 unfold listrep at 1. simpl app. Exists y. entailer!.
}
(* else-clause *)
assert_PROP (s1 <> nil). {
   unfold listrep at 1. 
   entailer!.  intuition.
  }
destruct s1 as [ | h r]; try congruence. clear H H0.
unfold listrep at 1; fold listrep.
Intros u.
forward.
forward.
forward_while 
   (EX u:val, EX t:val, EX s': list val, 
    EX i: val, EX r': list val,
    PROP (s' ++ [i] ++ r' = [h] ++ r)
    LOCAL (temp _u u; temp _t t; temp _x x; temp _y y)
    SEP (lseg s' x t; lseg [i] t u; listrep r' u; listrep s2 y)).
* (* Prove that the precondition implies the loop invariant *)
 Exists u x (@nil val) h r. 
 entailer. (* Cannot use entailer! here. *)
 apply sepcon_derives; auto.
 apply derives_trans with (emp * (lseg [h] x u * listrep r u)).
 cancel.
 unfold lseg. apply allp_right; intro s'. apply wand_sepcon_adjoint.
 simpl.
 unfold listrep at 2; fold listrep. Exists u; cancel.
 rewrite sepcon_assoc. apply sepcon_derives; auto.
 unfold lseg. apply allp_right; intro s'. apply wand_sepcon_adjoint.
 simpl. cancel.
* (* Prove that the loop test can evaluate *)
 entailer!.
* (* Prove the function body preserves the invariant *)
 forward.
 assert_PROP (r' <> nil) by (entailer!; intuition).
 destruct r' as [ | j r']; try congruence. clear H0.
 unfold listrep at 1; fold listrep.
 Intros z.
 forward.
 Exists (z,u0,s'++[i],j,r').
 entailer!.
 rewrite app_ass; auto.
 sep_apply (lseg_app s' [i] x t u0).
 cancel.
 unfold lseg. apply allp_right; intro. simpl.
 apply wand_sepcon_adjoint.
 unfold listrep at 2; fold listrep.
 Exists z. cancel.
 * (* After the loop *)
subst u0.
assert_PROP (r'=nil) by (entailer!; intuition).
subst r'.
rewrite lseg_nullval.
rewrite <- app_nil_end in H.
rename s' into s.
unfold listrep at 1 2.
Intros p. subst p.
forward.
forward.
Exists x.
entailer!.
change (h :: r ++ s2) with (([h]++r)++s2).
rewrite <- H.
rewrite app_ass.
clear.
assert (data_at Tsh t_list (i, y) t * listrep s2 y |--
           listrep (i::s2) t).
 unfold listrep at 2; fold listrep; Exists y; cancel.            sep_apply H; clear H.                                           
simpl.
unfold lseg. allp_left (i::s2). 
sep_apply (modus_ponens_wand (listrep (i::s2) t) (listrep (s++i::s2) x)).
auto.
Qed.
