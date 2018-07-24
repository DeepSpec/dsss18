(** * Verif_hash: Correctness proof of hash.c *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import  hash.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import Hashfun.

(* ================================================================= *)
(** ** Function specifications *)
(* ----------------------------------------------------------------- *)
(** *** Imports from the C string library *)

Definition strcmp_spec :=
 DECLARE _strcmp
  WITH str1 : val, s1 : string, str2 : val, s2 : string
  PRE [ 1 OF tptr tschar, 2 OF tptr tschar ]
    PROP ()
    LOCAL (temp 1 str1; temp 2 str2)
    SEP (cstring Tsh s1 str1; cstring Tsh s2 str2)
  POST [ tint ]
   EX i : int,
    PROP (if Int.eq_dec i Int.zero then s1 = s2 else s1 <> s2)
    LOCAL (temp ret_temp (Vint i))
    SEP (cstring Tsh s1 str1; cstring Tsh s2 str2).

Definition strcpy_spec :=
 DECLARE _strcpy
  WITH dest : val, n : Z, src : val, s : string
  PRE [ 1 OF tptr tschar, 2 OF tptr tschar ]
    PROP (Zlength s < n)
    LOCAL (temp 1 dest; temp 2 src)
    SEP (data_at_ Tsh (tarray tschar n) dest; cstring Tsh s src)
  POST [ tptr tschar ]
    PROP ()
    LOCAL (temp ret_temp dest)
    SEP (cstringn Tsh s n dest; cstring Tsh s src).

Definition strlen_spec :=
 DECLARE _strlen
  WITH s : string, str: val
  PRE [ 1 OF tptr tschar ]
    PROP ( )
    LOCAL (temp 1 str)
    SEP (cstring Tsh s str)
  POST [ tptr tschar ]
    PROP ()
    LOCAL (temp ret_temp (Vptrofs (Ptrofs.repr (Zlength s))))
    SEP (cstring Tsh s str).

(* ----------------------------------------------------------------- *)
(** ***  String functions:  copy, hash *)

Definition copy_string_spec : ident * funspec :=
 DECLARE _copy_string
 WITH s: val, sigma : string
 PRE [ _s OF tptr tschar ] 
    PROP ( ) LOCAL (temp _s s) SEP (cstring Tsh sigma s)
 POST [ tptr tschar ] 
    EX p: val, PROP ( ) LOCAL (temp ret_temp p) 
    SEP (cstring Tsh sigma s; cstring Tsh sigma p).

Definition hash_spec : ident * funspec :=
  DECLARE _hash
  WITH s: val, contents : string
  PRE [ _s OF (tptr tschar) ]
          PROP  ()
          LOCAL (temp _s s)
          SEP   (cstring Tsh contents s)
  POST [ tuint ]
        PROP ()
	LOCAL(temp ret_temp  (Vint (Int.repr (hashfun contents))))
        SEP (cstring Tsh contents s).

(* ----------------------------------------------------------------- *)
(** *** Data structures for hash table *)

Definition tcell := Tstruct _cell noattr.
Definition thashtable := Tstruct _hashtable noattr.

Definition list_cell (key: string) (count: Z) (next: val) (p: val): mpred :=
 EX kp: val, cstring Tsh key kp * data_at Tsh tcell (kp,(Vint (Int.repr count), next)) p 
                     * malloc_token Tsh tcell p.

Definition list_cell_local_facts: 
  forall key count next p, list_cell key count next p |-- !! isptr p.
Proof. intros. unfold list_cell. Intros kp. entailer!. Qed.
Hint Resolve list_cell_local_facts: saturate_local.

Definition list_cell_valid_pointer:
  forall key count next p, list_cell key count next p |-- valid_pointer p.
Proof. intros. unfold list_cell. Intros kp. entailer!. Qed.
Hint Resolve list_cell_valid_pointer: valid_pointer.

(** **** Exercise: 1 star (listcell_fold)  *)
Lemma listcell_fold: forall key kp count p' p,
  cstring Tsh key kp * data_at Tsh tcell (kp, (Vint (Int.repr count), p')) p * malloc_token Tsh tcell p 
         |-- list_cell key count p' p.
Proof. 
(* FILL IN HERE *) Admitted.
(** [] *)

Fixpoint listrep (sigma: list (string * Z)) (x: val) : mpred :=
 match sigma with
 | (s,c)::hs => EX y: val, list_cell s c y x * listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.

(** **** Exercise: 2 stars (listrep_hints)  *)
Lemma listrep_local_prop: forall sigma p, listrep sigma p |--
        !! (is_pointer_or_null p  /\ (p=nullval <-> sigma=nil)).
Proof.
(* FILL IN HERE *) Admitted.
Hint Resolve listrep_local_prop : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
(* FILL IN HERE *) Admitted.
Hint Resolve listrep_valid_pointer : valid_pointer.
(** [] *)

Lemma listrep_fold: forall key count p' p al, 
  list_cell key count p' p * listrep al p' |-- listrep ((key,count)::al) p.
Proof. intros. simpl. Exists p'. cancel. Qed.

Definition listboxrep al r :=
 EX p:val, data_at Tsh (tptr tcell) p r * listrep al p.

Definition uncurry {A B C} (f: A -> B -> C) (xy: A*B) : C :=
  f (fst xy) (snd xy).

Definition hashtable_rep (contents: hashtable_contents) (p: val) : mpred :=
  EX bl: list (list (string * Z) * val),
    !! (contents = map fst bl) &&
    malloc_token Tsh thashtable p * 
    field_at Tsh thashtable [StructField _buckets] (map snd bl) p 
    * iter_sepcon (uncurry listrep) bl.

(** **** Exercise: 2 stars (hashtable_rep_hints)  *)
Lemma hashtable_rep_local_facts: forall contents p,
 hashtable_rep contents p |-- !! (isptr p /\ Zlength contents = N).
(* FILL IN HERE *) Admitted.
Hint Resolve hashtable_rep_local_facts : saturate_local.

Lemma hashtable_rep_valid_pointer: forall contents p,
 hashtable_rep contents p |-- valid_pointer p.
(* FILL IN HERE *) Admitted.
Hint Resolve hashtable_rep_valid_pointer : valid_pointer.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Function specifications for hash table *)

Definition new_table_spec : ident * funspec :=
 DECLARE _new_table
 WITH u: unit
 PRE [ ] 
   PROP()
   LOCAL()
   SEP()
 POST [ tptr thashtable ] 
   EX p:val, PROP() 
      LOCAL(temp ret_temp p) 
      SEP(hashtable_rep empty_table p).

Definition new_cell_spec : ident * funspec :=
 DECLARE _new_cell
 WITH s: val, key: string, count: Z, next: val
 PRE [ _key OF tptr tschar, _count OF tint, _next OF tptr tcell ] 
   PROP()
   LOCAL(temp _key s; temp _count (Vint (Int.repr count)); temp _next next)
   SEP(cstring Tsh key s)
 POST [ tptr tcell ] 
   EX p:val, PROP() 
      LOCAL(temp ret_temp p) 
      SEP(list_cell key count next p; cstring Tsh key s).

Definition get_spec : ident * funspec :=
 DECLARE _get
 WITH p: val, contents: hashtable_contents, s: val, sigma : string
 PRE [ _table OF tptr (Tstruct _hashtable noattr), _s OF tptr tschar ] 
    PROP () 
    LOCAL (temp _table p; temp _s s)
    SEP (hashtable_rep contents p; cstring Tsh sigma s)
 POST [ tuint ]
      PROP ( ) LOCAL (temp ret_temp (Vint (Int.repr (hashtable_get sigma contents))))
      SEP (hashtable_rep contents p; cstring Tsh sigma s).

Definition incr_list_spec : ident * funspec :=
 DECLARE _incr_list
 WITH r0: val, al: list (string * Z), s: val, sigma : string
 PRE [ _r0 OF tptr (tptr tcell), _s OF tptr tschar ] 
    PROP (list_get sigma al < Int.max_unsigned) 
    LOCAL (temp _r0 r0; temp _s s)
    SEP (listboxrep al r0; cstring Tsh sigma s)
 POST [ tvoid ]
      PROP ( ) LOCAL ()
      SEP (listboxrep (list_incr sigma al) r0; cstring Tsh sigma s).

Definition incr_spec : ident * funspec :=
 DECLARE _incr
 WITH p: val, contents: hashtable_contents, s: val, sigma : string
 PRE [ _table OF tptr (Tstruct _hashtable noattr), _s OF tptr tschar ] 
    PROP (hashtable_get sigma contents < Int.max_unsigned) 
    LOCAL (temp _table p; temp _s s)
    SEP (hashtable_rep contents p; cstring Tsh sigma s)
 POST [ tvoid ]
      PROP ( ) LOCAL ()
      SEP (hashtable_rep (hashtable_incr sigma  contents) p; cstring Tsh sigma s).

(**  Putting all the funspecs together *)

Definition Gprog : funspecs :=
        ltac:(with_library prog [
                   strcmp_spec; strcpy_spec; strlen_spec; hash_spec;
                   new_cell_spec; copy_string_spec; get_spec; incr_spec; 
                   incr_list_spec
 ]).

(* ================================================================= *)
(** ** Proofs of the function bodies *)

(** This lemma demonstrates how to handle "strings", that is,
   null-terminated arrays of characters. *)
Lemma demonstrate_cstring1: 
 forall i contents,
   ~ In Byte.zero contents ->
   Znth i (contents ++ [Byte.zero]) <> Byte.zero  ->
   0 <= i <= Zlength contents ->
   0 <= i + 1 < Zlength (contents ++ [Byte.zero]).
Proof.
intros.
(** When processing a C null-terminated string, you will want to
   maintain the three kinds of assumptions above the line.
   A string is an array of characters with three parts:
   - The "contents" of the string, none of which is the '\0' character;
   - The null termination character, equal to Byte.zero;
   - the remaining garbage in the array, after the null.
  The first assumption above the line says that none of the
  contents is the null character. 
  Now suppose we are in a loop where variable [_i] (with value [i])
  is traversing the array.  We expect that loop to go up to but 
  no farther than the null character, that is, one past the contents.
  Therefore [0 <= i <= Zlength contents].
  Furthermore, suppose we have determined (by an if-test) that
  s[i] is not zero, then we have the hypothesis H0 above.

  The [cstring] tactic processes all three of them to conclude
  that [i < Zlength contents]. *)
assert (H7: i < Zlength contents) by cstring.

(** But actually, [cstring] tactic will prove any rep_omega consequence
   of that fact.  For example: *)
clear H7.
autorewrite with sublist.
cstring.
Qed.
(** Don't apply [demonstrate_cstring1] in the body_hash proof, 
    instead, use [autorewrite with sublist] and [cstring] directly, 
    where appropriate. *)

Lemma demonstrate_cstring2: 
 forall i contents,
   ~ In Byte.zero contents ->
   Znth i (contents ++ [Byte.zero]) = Byte.zero  ->
   0 <= i <= Zlength contents ->
   i = Zlength contents.
Proof.
intros.
(** Here is another demonstration.  When your loop on the
   string contents reaches the end, so that s[i] is the zero byte,
   you'll have the an assumption like [H0] above the line.
   The [cstring] tactic handles this case too, to prove 
   [i = Zlength contents].   *)
cstring.
Qed.

(** **** Exercise: 3 stars (body_hash)  *)
Lemma body_hash: semax_body Vprog Gprog f_hash hash_spec.
Proof.
start_function.
unfold cstring,hashfun in *.
(** Before doing this proof, study some of the proofs in VST/progs/verif_strlib.v.
  In the PROP part of your loop invariant, you'll want to maintain [0 <= i <= Zlength contents].

  In the LOCAL part of your loop invariant, try to use something like

    temp _c (Vbyte (Znth i (contents ++ [Byte.zero]))

  instead of 

    temp _c (Znth 0 (map Vbyte (...)))

  The reason is that [temp _c (Vint x)] or [temp _c (Vbyte y)] is much easier
  for Floyd to handle than [temp _c X]
  where X is a general formula of type [val].
 
  Late in the proof of the loop body, the lemma [hashfun_snoc] will be useful. *)
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (body_new_cell)  *)
Lemma body_new_cell: semax_body Vprog Gprog f_new_cell new_cell_spec.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Auxiliary lemmas about data-structure predicates *)


(** **** Exercise: 2 stars (iter_sepcon_hints)  *)
Lemma iter_sepcon_listrep_local_facts:
 forall bl, iter_sepcon (uncurry listrep) bl
                    |-- !! Forall is_pointer_or_null (map snd bl).
Proof.
(* Hint: use [induction] and [sep_apply]. *)
(* FILL IN HERE *) Admitted.

Hint Resolve iter_sepcon_listrep_local_facts : saturate_local.
(** [] *)

(** **** Exercise: 2 stars (iter_sepcon_split3)  *)
Lemma iter_sepcon_split3: 
  forall {A}{d: Inhabitant A} (i: Z) (al: list A) (f: A -> mpred),
   0 <= i < Zlength al   -> 
  iter_sepcon f al = 
  iter_sepcon f (sublist 0 i al) * f (Znth i al) * iter_sepcon f (sublist (i+1) (Zlength al) al).
Proof.
intros.
rewrite <- (sublist_same 0 (Zlength al) al) at 1 by auto.
(* Hint: [rewrite (sublist_split LO MID HI) by omega], where you choose values for LO MID HI. 
  Also useful:  [rewrite sublist_len_1]    and    [iter_sepcon_app].
*)
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (body_new_table)  *)
Lemma body_new_table_helper: 
 (* This lemma is useful as the very last thing to do in body_new_table *)
 forall p, 
  data_at Tsh thashtable (list_repeat (Z.to_nat N) nullval) p
  |-- field_at Tsh thashtable [StructField _buckets]
       (list_repeat (Z.to_nat N) nullval) p *
         iter_sepcon (uncurry listrep) (list_repeat (Z.to_nat N) ([], nullval)).
Proof.
intros.
unfold_data_at 1%nat.
(* FILL IN HERE *) Admitted.

Lemma body_new_table: semax_body Vprog Gprog f_new_table new_table_spec.
Proof.
(** The loop invariant in this function describes a partially initialized array.
   The best way to do that is with something like,

  data_at Tsh thashtable 
      (list_repeat (Z.to_nat i) nullval ++ 
       list_repeat (Z.to_nat (N-i)) Vundef)   p.

  Then at some point you'll have to prove something about,

   data_at Tsh thashtable
      (list_repeat (Z.to_nat (i + 1)) nullval ++ 
       list_repeat (Z.to_nat (N - (i + 1))) Vundef)   p

  In particular, you'll have to split up [list_repeat (Z.to_nat (i + 1)) nullval]
   into [list_repeat (Z.to_nat i) nullval ++ list_repeat (Z.to_nat 1) nullval].
  The best way to do that is [rewrite <- list_repeat_app'.]
*)
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (body_get)  *)
(** The [get] function traverses a linked list.  We will reason about linked-list traversal
   in separation logic using "Magic Wand as Frame" http://www.cs.princeton.edu/~appel/papers/wand-frame.pdf
   When the loop is partway down the linked list, we can view the original list
   up to the current position as a "linked-list data structure with a hole";
   and the current position points to a linked-list data structure that fills the hole.
   The "data-structure-with-a-hole" we reason about with separating implication,
    called "magic wand":   (hole -* data-structure)
    which says, if you can conjoin this data-structure-with-a-hole 
    with something-to-fill-the-hole, then you get the original data structure:
     hole * (hole -* data-structure) |--   data-structure.
    The lemma [listrep_traverse] is useful in moving one linked-list cell
    out of the hole and into the data-structure-with-a-(smaller)-hole.
*)

Lemma listrep_traverse:  (* useful in body_get lemma*)
  forall key count p' p, 
  list_cell key count p' p |-- 
  ALL al:list (string * Z), listrep al p' -* (EX y : val, list_cell key count y p * listrep al y).
Proof.
intros.
apply allp_right; intro al.
(* FILL IN HERE *) Admitted.

Lemma body_get: semax_body Vprog Gprog f_get get_spec.
Proof.
start_function.
rename p into table.
pose proof (hashfun_inrange sigma).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (listboxrep_traverse)  *)
Lemma listboxrep_traverse:
  forall p kp key count r, 
          field_compatible tcell [] p ->
            cstring Tsh key kp * 
            field_at Tsh tcell [StructField _key] kp p *
            field_at Tsh tcell [StructField _count] (Vint (Int.repr count)) p *
            malloc_token Tsh tcell p *
            data_at Tsh (tptr tcell) p r |-- 
            ALL dl: list (string * Z), 
              listboxrep dl (field_address tcell [StructField _next] p)
                -* listboxrep ((key, count) :: dl) r.
Proof.
   intros.
  apply allp_right; intro dl.
   apply -> wand_sepcon_adjoint.
   (** Sometime during the proof below, you will have
       [data_at Tsh tcell ... p]
     that you want to expand into 

       field_at Tsh tcell [StructField _key] ... p 
     * field_at Tsh tcell [StructField _count] ... p 
     * field_at Tsh tcell [StructField _next] ... p]. 

   You can do this with   [unfold_data_at x%nat] where x is the number
   indicating _which_ of the [data_at] or [field_at] conjucts you want to expand.
*)

(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (body_incr_list)  *)
Lemma body_incr_list: semax_body Vprog Gprog f_incr_list incr_list_spec.
Proof.
(** This proof uses "magic wand as frame" to traverse _and update_ 
   a (linked list) data structure.   This pattern is a bit more complex than
   the wand-as-frame pattern used in body_get, which did not update
   the data structure.   You will still use "data-structure-with-a-hole"
   and "what-is-in-the-hole"; but now the "data-structure-with-a-hole"
   must be able to accept the _future_ hole-filler, not the one that is
   in the hole right now.

  The key lemmas to use are, [wand_refl_cancel_right], [wand_frame_elim'],
   and [wand_frame_ver].   When using [wand_frame_ver], you will find
   [listboxrep_traverse] to be useful.
*)
(* FILL IN HERE *) Admitted.
(** [] *)


Lemma field_at_data_at':
      forall {cs: compspecs} (sh : Share.t) (t : type) (gfs : list gfield)
         (v : reptype (nested_field_type t gfs)) 
         (p : val),
       field_at sh t gfs v p =
       !! field_compatible t gfs p  && data_at sh (nested_field_type t gfs) v (field_address t gfs p).
Proof.
intros.
apply pred_ext.
entailer!. rewrite field_at_data_at; auto.
entailer!. rewrite field_at_data_at; auto.
Qed.

(** Examine this carefully: *)
Check wand_slice_array.
(*  : forall (lo hi n : Z) (t : type) (sh : Share.t)
             (al' : list (reptype t)) (p : val),
       0 <= lo <= hi ->
       hi <= n ->
       Zlength al' = n ->
       data_at sh (tarray t n) al' p =
       !! field_compatible (tarray (tptr tcell) n) [] p &&
       data_at sh (tarray t (hi - lo)) 
         (sublist lo hi al')
         (field_address0 (tarray t n) [ArraySubsc lo] p) *
       array_with_hole sh t lo hi n al p.
*)
(** Here (array_with_hole sh t lo hi n al p) means *)
(*  :  (ALL cl : list (reptype t) ,
         data_at sh (tarray t (hi - lo)) cl
           (field_address0 (tarray t n) [ArraySubsc lo] p) -*
         data_at sh (tarray t n)
           (sublist 0 lo al' ++ cl ++ sublist hi n al') p)
*)

(** **** Exercise: 4 stars (body_incr)  *)
Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
start_function.
rename p into table.
rename H into Hmax.
assert_PROP (isptr table) as Htable by entailer!.

(** The next two lines would not be part of an ordinary Verifiable C proof, 
   they are here only to guide you through the bigger proof. *)
match goal with |- semax _ _ (Ssequence (Ssequence ?c1 (Ssequence ?c2 ?c3)) ?c4) _ => apply (semax_unfold_seq (Ssequence (Ssequence c1 c2) (Ssequence c3 c4))); [ reflexivity | ] end;
pose (j := EX cts: list (list (string * Z) * val), PROP (contents = map fst cts; 0 <= hashfun sigma mod N < N; Zlength cts = N) LOCAL (temp _b (Vint (Int.repr (hashfun sigma mod N))); temp _h (Vint (Int.repr (hashfun sigma))); temp _table table; temp _s s) SEP (cstring Tsh sigma s; malloc_token Tsh thashtable table; data_at Tsh (tarray (tptr tcell) N) (map snd cts) (field_address thashtable [StructField _buckets] table); iter_sepcon (uncurry listrep) cts)); apply semax_seq' with j; subst j; abbreviate_semax.
{
 (* FILL IN HERE *) admit.
 }

Intros cts.
subst contents.
unfold hashtable_get in Hmax.
rewrite Zlength_map, H1 in Hmax.
set (h := hashfun sigma mod N) in *. 
erewrite (wand_slice_array h (h+1) N _ (tptr tcell))
  by first [rep_omega | list_solve ].

(** For the remainder of the proof, here are some useful lemmas:
    [sublist_len_1] [sublist_same] [sublist_map]
    [data_at_singleton_array_eq]
    [iter_sepcon_split3]  [iter_sepcon_app] [sublist_split]
    [field_at_data_at]
    [wand_slice_array_tptr_tcell]
*)

 (* FILL IN HERE *) admit.
(* FILL IN HERE *) Admitted.
(** [] *)
