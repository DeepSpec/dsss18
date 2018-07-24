(** * Verif_triang: A client of the stack functions *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import  stack.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* ================================================================= *)
(** ** Proofs with integers *)

(** The natural numbers have arithmetic axioms that are not very nice.
   For example, you might expect that [a-b+b=a], but that's not true: *)
Lemma nat_sub_add_yuck:
  ~ (forall a b: nat, a-b+b=a)%nat.
Proof.
intros.
intro.
specialize (H 0 1)%nat.
simpl in H. inversion H.
Qed.

(**  This just shows that if the negative numbers did not exist, it would be 
      necessary to construct them!  In reasoning about programs, as in many other
      kinds of mathematics, we should use the integers.  In Coq the type is called [Z]. *)
Lemma Z_sub_add_ok:
  forall a b : Z, a-b+b=a.
Proof. intros. omega. Qed.

(** The Z type does have an inductive definition . . . *)
Print Z.
(* Inductive Z : Set := Z0 : Z | Zpos : positive -> Z | Zneg : positive -> Z *)
(** but we generally prefer to reason _abstractly_ about Z, using the lemmas
     in the Coq library (that the Coq developers proved from the inductive definition).
    In fact, the natural induction principle on Z is not the one we usually want to use! *)

(** Let's consider a recursive function on Z, the function that turns [5] into the 
   list [5::4::3::2::1::nil].  In the natural numbers, that's easy to define: *)

Fixpoint decreasing_nat (n: nat) : list nat := 
 match n with S n' => n :: decreasing_nat n' | O => nil end.

(** But in the integers [Z], we cannot simply pattern-match on successor . . . *)
Fail Fixpoint decreasing_Z (n: Z) : list Z := 
 match n with Z.succ n' => n :: decreasing_Z n' | 0 => nil end.
(** . . . because Z.succ is a function, not a constructor. *)

(** There are two ways we might define a function to produce a decreasing list of Z.
  First, we might use [Z.of_nat] and [Z.to_nat]:  *)

Fixpoint decreasing_Z1_aux (n: nat) : list Z := 
 match n with S n' => Z.of_nat n :: decreasing_Z1_aux n' | O => nil end.
Definition decreasing_Z1 (n: Z) : list Z := decreasing_Z1_aux (Z.to_nat n).

(** This will work, but in doing proofs the frequent conversion between Z and nat
   will be awkward.  If possible, we'd like to stay in the integers as much as possible.
   So here's another way: *)

Check Z_gt_dec. (*   : forall x y : Z, {x > y} + {~ x > y} *)

Function decreasing (n: Z) {measure Z.to_nat n}:= 
 if Z_gt_dec n 0 then n :: decreasing (n-1) else nil.
Proof.
(** When you define a Function, you must provide a [measure], that is, a function
    from your argument-type (in this case Z) to the natural numbers, and then you 
    must prove that each recursive call within the function body decreases the measure.
    In this ecase, there's only one recursive call, so there's just one proof obligation:
     show that [n>0 -> Z.to_nat (n-1) < Z.to_nat n]. *)
intros.
apply Z2Nat.inj_lt; omega.
Defined.  (* Terminate your [Function] declarations with [Defined] instead of [Qed],
 so that Coq will be able to use your function in computations. *)

(** **** Exercise: 2 stars (Zinduction)  *)
(** Coq's standard induction principle for Z is not the one we usually want, so let us
   define a more natural induction scheme: *)
Lemma Zinduction: forall  (P: Z -> Prop),
  P 0 ->
  (forall i, 0 < i -> P (i-1) -> P i) ->
  forall n, 0 <= n -> P n.
Proof.
intros.
rewrite <- (Z2Nat.id n) in * by omega.
remember (Z.to_nat n) as j. clear Heqj.
Check inj_S.  (* Hint!  this may be useful *)
Print Z.succ.  (* Hint!  [Z.succ(x)] unfolds to [x+1] *)
(* FILL IN HERE *) Admitted.
(** [] *)


(* ----------------------------------------------------------------- *)
(** *** A theorem about the nth triangular number *)

Definition add_list: list Z -> Z := fold_right Z.add 0.

(** **** Exercise: 2 stars (add_list_decreasing)  *)

(** Theorem:  the sum of the list  [(n)::(n-1):: ... :: 2::1] is the triangular number of [n]. *)

Lemma add_list_decreasing_eq_alt: forall n,
  0 <= n ->
  (2 * (add_list (decreasing n)))%Z = (n * (n+1))%Z.
Proof.
  intros.
  pattern n; apply Zinduction.
  - reflexivity.
  - intros.
(** WARNING!  When using functions defined by [Function], don't unfold them!
   Temporarily remove the (* comment *) brackets from the next line to see what happens! *)
(*  unfold decreasing. *)

(** Instead of unfolding [decreasing] we use the equation that Coq automagically defines
   for the Function.  Go back up and reprocess the [Defined.] line that terminated
   [Function decreasing], and notice what happens in Coq's error-message window:
   it says that lots of additional reasoning principles are defined for the new [Function].
   (For some reason, Coq 8.8 does not mention [decreasing_equation], but it is
    defined at the same time as the others.)  *)
Check decreasing_equation.

    rewrite decreasing_equation.

(** during the proof of this lemma, you may
find the [ring_simplify] tactic useful.  Read
about it in the Coq reference manual.  Basically,
it takes formulas with multiplication and addition,
and simplifies them.  But you can do this without
[ring_simplify], using just ordinary rewriting
with lemmas about Z.add and Z.mul.  *)
(* FILL IN HERE *) Admitted.

Lemma add_list_decreasing_eq: forall n,
  0 <= n ->
  add_list (decreasing n) = n * (n+1) / 2.
Proof.
  intros.
  apply Z.div_unique_exact.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Definitions copied from Verif_stack.v *)
(** We repeat here some material from Verif_stack.v.  
   Normally we would break the .c file into separate modules,
  and do our Verifiable C proofs in separate modules;
  but for this example we leave out the modules. *)

(**  Specification of linked lists in separation logic *)

Fixpoint listrep (il: list Z) (p: val) : mpred :=
 match il with
 | i::il' => EX y: val, 
        malloc_token Tsh (Tstruct _cons noattr) p *
        data_at Tsh (Tstruct _cons noattr) (Vint (Int.repr i),y) p * listrep il' y
 | nil => !! (p = nullval) && emp
 end.

Lemma listrep_local_prop: forall il p, listrep il p |--
        !! (is_pointer_or_null p  /\ (p=nullval <-> il=nil)).
Proof.
induction il; intro; simpl.
entailer!. intuition.
Intros y.
entailer!.
split; intros. subst.
eapply field_compatible_nullval; eauto.
inversion H3.
Qed.
Hint Resolve listrep_local_prop : saturate_local.

Lemma listrep_valid_pointer:
  forall il p,
   listrep il p |-- valid_pointer p.
Proof.
(* FILL IN HERE *) Admitted.
Hint Resolve listrep_valid_pointer : valid_pointer.

(** Specification of stack data structure *)

Definition stack (il: list Z) (p: val) :=
 EX q: val,
  malloc_token Tsh (Tstruct _stack noattr) p * 
  data_at Tsh (Tstruct _stack noattr) q p * listrep il q.

Lemma stack_local_prop: forall il p, stack il p |--  !! (isptr p).
Proof.
(* FILL IN HERE *) Admitted.
Hint Resolve stack_local_prop : saturate_local.

Lemma stack_valid_pointer:
  forall il p,
   stack il p |-- valid_pointer p.
Proof.
(* FILL IN HERE *) Admitted.
Hint Resolve stack_valid_pointer : valid_pointer.

Definition newstack_spec : ident * funspec :=
 DECLARE _newstack
 WITH tt: unit
 PRE [ ] 
    PROP () LOCAL () SEP ()
 POST [ tptr (Tstruct _stack noattr) ] 
    EX p: val, PROP ( ) LOCAL (temp ret_temp p) SEP (stack nil p).

Definition push_spec : ident * funspec :=
 DECLARE _push
 WITH p: val, i: Z, il: list Z
 PRE [ _p OF tptr (Tstruct _stack noattr), _i OF tint ] 
    PROP (Int.min_signed <= i <= Int.max_signed) 
    LOCAL (temp _p p; temp _i (Vint (Int.repr i))) 
    SEP (stack il p)
 POST [ tvoid ] 
    PROP ( ) LOCAL () SEP (stack (i::il) p).

Definition pop_spec : ident * funspec :=
 DECLARE _pop
 WITH p: val, i: Z, il: list Z
 PRE [ _p OF tptr (Tstruct _stack noattr) ] 
    PROP () 
    LOCAL (temp _p p) 
    SEP (stack (i::il) p)
 POST [ tint ] 
    PROP ( ) LOCAL (temp ret_temp (Vint (Int.repr i))) SEP (stack il p).

(** (End of the material repeated from Verif_stack.v) *)

(* ================================================================= *)
(** ** Specification of the stack-client functions *)

Definition push_increasing_spec :=
 DECLARE _push_increasing
 WITH st: val, n: Z
 PRE [ _st OF tptr (Tstruct _stack noattr), _n OF tint ]
   PROP (0 <= n <= Int.max_signed)
   LOCAL (temp _st st; temp _n (Vint (Int.repr n)))
   SEP (stack nil st)
 POST [ tvoid ]
   PROP() LOCAL() SEP (stack (decreasing n) st).

Definition pop_and_add_spec :=
 DECLARE _pop_and_add
 WITH st: val, il: list Z
 PRE [ _st OF tptr (Tstruct _stack noattr), _n OF tint ]
   PROP (Zlength il <= Int.max_signed;
             Forall (Z.le 0) il;
             add_list il <= Int.max_signed)
   LOCAL (temp _st st; temp _n (Vint (Int.repr (Zlength il))))
   SEP (stack il st)
 POST [ tint ]
   PROP() 
   LOCAL(temp ret_temp (Vint (Int.repr (add_list il))))
   SEP (stack nil st).

Definition main_spec :=
 DECLARE _main
 WITH gv: globals
 PRE [ ] main_pre prog nil gv
 POST [ tint ] 
   PROP( ) LOCAL (temp ret_temp (Vint (Int.repr 55))) SEP( TT ).

(** Putting all the funspecs together *)

Definition Gprog : funspecs :=
        ltac:(with_library prog [
                   newstack_spec; push_spec; pop_spec; 
                   push_increasing_spec; pop_and_add_spec; main_spec
 ]).

(* ================================================================= *)
(** ** Proofs of the stack-client function-bodies *)

(** **** Exercise: 3 stars (body_push_increasing)  *)
Lemma body_push_increasing: semax_body Vprog Gprog f_push_increasing push_increasing_spec.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (add_list_lemmas)  *)
Lemma add_list_app:
  forall al bl, add_list (al++bl) = add_list al + add_list bl.
(* FILL IN HERE *) Admitted.

Lemma add_list_nonneg:
 forall il,
  Forall (Z.le 0) il ->
  0 <= add_list il.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (add_list_sublist_bounds)  *)
Lemma add_list_sublist_bounds:
 forall lo hi K il,
  0 <= lo <= hi ->
  hi <= Zlength il ->
  Forall (Z.le 0) il ->
  0 <= add_list il <= K ->
  0 <= add_list (sublist lo hi il) <= K.
Proof.
(** Hint: you don't need induction.  Useful lemmas are,
  [sublist_same, sublist_split, add_list_nonneg, add_list_app, Forall_sublist]
  and use the [hint] tactic to learn when the [list_solve] tactic will be useful. *)
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (add_another)  *)
(** Suppose we have a list [il] of integers, [il = [5;4;3;2;1]],
   with [Znth 0 il = 5], [Znth 4 il = 1], and [Zlength il = 5],
   and we want to add them all up,  5+4+3+2+1=15.
  Suppose we've already added up the first [i] of them  (let [i=2] for example),
  that is, 5+4=9, and we want to add the next one, that is, the [ith] one.
  That is, we want to add [9+3].  How do we know that won't overflow
  the range of C-language signed integer arithmetic?  
    The proof goes:  Every element of the list is nonnegative; the whole
   list adds up to a number <= Int.max_signed; and any sublist of an
   all-nonnegative list adds up to less-or-equal to the total of the whole list.
*)

Lemma add_another:
 forall il, 
   Forall (Z.le 0) il ->
   add_list il <= Int.max_signed ->
  forall i : Z,
  0 <= i < Zlength il ->
  Int.min_signed <= Int.signed (Int.repr (add_list (sublist 0 i il))) +
           Int.signed (Int.repr (Znth i il)) <= Int.max_signed.
Proof.
intros.
assert (0 <= add_list il). {
  (* FILL IN HERE *) admit. 
}
 assert (0 <= add_list (sublist 0 i il) <= Int.max_signed). {
   split.
  (* FILL IN HERE *) admit. 
  (* FILL IN HERE *) admit. 
 }
 assert (0 <= add_list (sublist (i+1) (Zlength il) il) <= Int.max_signed). {
   split.
  (* FILL IN HERE *) admit. 
  (* FILL IN HERE *) admit. 
 }
 assert (0 <= Znth i il <= Int.max_signed). {
   split.
  (* FILL IN HERE *) admit. 
  (** To do the next proof, split up [add_list il] in hypothesis [H0] into 
   [add_list (sublist 0 i il) + Znth i il + add_list (sublist (i + 1) (Zlength il) il)]
   using the lemmas [sublist_same, sublist_split, add_list_app, sublist_len_1],
   then use [omega]. *)
   rewrite <- (sublist_same 0 (Zlength il) il) in H0 by omega.
   rewrite (sublist_split 0 i (Zlength il)) in H0 by list_solve.
  (* FILL IN HERE *) admit. 
 }

(**   Next: [Int.signed (Int.repr (add_list (sublist 0 i il))) = add_list (sublist 0 i il)].
   To prove that, we'll use [Int.signed_repr]:
*)
Check Int.signed_repr.
(**   :   forall z : Z,   Int.min_signed <= z <= Int.max_signed -> 
                     Int.signed (Int.repr z) = z. *)
 rewrite Int.signed_repr by rep_omega.
(** [rep_omega] is just like [omega], but it also knows the numeric values of
    representation-related constants such as Int.min_signed. *)
 rewrite Int.signed_repr by rep_omega.
 assert (0 <= add_list (sublist 0 (i+1) il) <= Int.max_signed). {
  (* FILL IN HERE *) admit. 
 }
  rewrite (sublist_split 0 i (i+1)) in H6 by list_solve.
  rewrite add_list_app in H6.
  rewrite sublist_len_1 in H6 by list_solve.
  simpl in H6.
  rep_omega.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (body_pop_and_add)  *)
Lemma body_pop_and_add: semax_body Vprog Gprog f_pop_and_add pop_and_add_spec.
Proof.
start_function.
forward.
forward.
forward_while (EX i:Z, 
   PROP(0 <= i <= Zlength il) 
   LOCAL (temp _st st; 
               temp _i (Vint (Int.repr i)); 
               temp _n (Vint (Int.repr (Zlength il))))
   SEP (stack (sublist i (Zlength il) il) st)).
(* FILL IN HERE *) admit.
+
entailer!.
+
forward_call (st, Znth i il, sublist (i+1) (Zlength il) il).
(** This [forward_call] couldn't quite figure out the "Frame" for the function call.
   That is, it couldn't match up  [stack (sublist i (Zlength il) il) st]
   with [stack (Znth i il :: sublist (i + 1) (Zlength il) il) st].
    You have to help, by doing some rewrites with [sublist_split, sublist_len_1]
    that prove [sublist i (Zlength il) il  =Znth i il :: sublist (i + 1) (Zlength il) il].
    When you've rewritten to the form,
   [ stack (Znth i il :: sublist (i + 1) (Zlength il) il) st
      |-- stack (Znth i il :: sublist (i + 1) (Zlength il) il) st * fold_right_sepcon Frame ],
    then just do [cancel].  *)
(* FILL IN HERE *) admit.
Fail forward.
(** oops!  we can't go [forward] through the statement  [ _s = _s + _t; ] 
    because we forgot to mention [temp _s] in the loop invariant!
   Time to start over.  

    By the way, this statement [ _s = _s + _t ] is exactly where [forward] will
   demand you prove the subgoal where the lemma [add_another] is useful. *)
Abort.

Lemma body_pop_and_add: semax_body Vprog Gprog f_pop_and_add pop_and_add_spec.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (body_main)  *)
Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)
