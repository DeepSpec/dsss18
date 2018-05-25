(** * Verif_strlib: String functions *)

(** THIS CHAPTER IS JUST A STUB RIGHT NOW. *)

(** This chapter should show how to prove the correctness
 of functions on C null-terminated character strings:
 strlen, strcmp, strcpy.
*)


(* ================================================================= *)
(** ** Here are some functions from the C standard library, [strlib.c] *)

(** 

#include <stddef.h>

size_t strlen(const char *str) {
  size_t i;
  for (i=0; ; i++)
    if (str[i]==0) return i;
}

char *strcpy(char *dest, const char *src) {
  size_t i;
  for(i = 0;; i++){
    char d = src[i];
    dest[i] = d;
    if(d == 0) return dest;
  }
}

int strcmp(const char *str1, const char *str2) {
  size_t i;
  for(i = 0;; i++){
    char d1 = str1[i];
    char d2 = str2[i];
    if(d1 == 0 && d2 == 0) return 0;
    else if(d1 < d2) return -1;
    else if(d1 > d2) return 1;
  }
}    
*)

(* ================================================================= *)
(** ** Standard boilerplate *)

Require Import VST.floyd.proofauto.
Require Import strlib.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* ================================================================= *)
(** ** Function specs *)

Definition strlen_spec :=
 DECLARE _strlen
  WITH s : list byte, str: val
  PRE [ _str OF tptr tschar ]
    PROP ( )
    LOCAL (temp _str str)
    SEP (cstring Tsh s str)
  POST [ tptr tschar ]
    PROP ()
    LOCAL (temp ret_temp (Vptrofs (Ptrofs.repr (Zlength s))))
    SEP (cstring Tsh s str).

Definition strcpy_spec :=
 DECLARE _strcpy
  WITH dest : val, n : Z, src : val, s : list byte
  PRE [ _dest OF tptr tschar, _src OF tptr tschar ]
    PROP (Zlength s < n)
    LOCAL (temp _dest dest; temp _src src)
    SEP (data_at_ Tsh (tarray tschar n) dest; cstring Tsh s src)
  POST [ tptr tschar ]
    PROP ()
    LOCAL (temp ret_temp dest)
    SEP (cstringn Tsh s n dest; cstring Tsh s src).

Definition strcmp_spec :=
 DECLARE _strcmp
  WITH str1 : val, s1 : list byte, str2 : val, s2 : list byte
  PRE [ _str1 OF tptr tschar, _str2 OF tptr tschar ]
    PROP ()
    LOCAL (temp _str1 str1; temp _str2 str2)
    SEP (cstring Tsh s1 str1; cstring Tsh s2 str2)
  POST [ tint ]
   EX i : int,
    PROP (if Int.eq_dec i Int.zero then s1 = s2 else s1 <> s2)
    LOCAL (temp ret_temp (Vint i))
    SEP (cstring Tsh s1 str1; cstring Tsh s2 str2).

Definition Gprog : funspecs :=
         ltac:(with_library prog [ strlen_spec; strcpy_spec; strcmp_spec ]).

(* ================================================================= *)
(** ** Proof of the [strlen] function *)

Lemma body_strlen: semax_body Vprog Gprog f_strlen strlen_spec.
Proof.
start_function.
unfold cstring in *.
rename s into ls.
Intros.
forward.
forward_loop  (EX i : Z,
  PROP (0 <= i < Zlength ls + 1)
  LOCAL (temp _str str; temp _i (Vptrofs (Ptrofs.repr i)))
  SEP (data_at Tsh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str)).
*
Exists 0. entailer!.
*
Intros i.
assert (Zlength (ls ++ [Byte.zero]) = Zlength ls + 1) by (autorewrite with sublist; auto).
forward.
normalize.
forward_if.
forward.
entailer!. f_equal. f_equal. cstring.
forward. (* entailer!.  *)
forward.
Exists (i+1).
entailer!. cstring.
Qed.

(* ================================================================= *)
(** ** Proof of the [strcpy] function *)

Lemma split_data_at_app:
 forall sh t n (al bl: list (reptype t)) abl'
         (al': reptype (tarray t (Zlength al)))
         (bl': reptype (tarray t (n - Zlength al)))
          p ,
   n = Zlength (al++bl) ->
   JMeq abl' (al++bl) ->
   JMeq al' al ->
   JMeq bl' bl ->
   data_at sh (tarray t n) abl' p = 
         data_at sh (tarray t (Zlength al)) al' p
        * data_at sh (tarray t (n - Zlength al)) bl'
                 (field_address0 (tarray t n) [ArraySubsc (Zlength al)] p).
Proof.
intros.
unfold tarray.
erewrite split2_data_at_Tarray.
4: rewrite sublist_same; [eassumption | auto | auto ].
4: rewrite sublist_app1.
4: rewrite sublist_same; [eassumption | auto | auto ].
2: rewrite Zlength_app in H by list_solve; list_solve.
2: rewrite Zlength_app in H by list_solve; list_solve.
2: list_solve.
2: omega.
2: rewrite sublist_app2.
2: rewrite sublist_same; [eassumption | auto | auto ].
auto.
all: rewrite Zlength_app in H; rep_omega.
Qed.

Lemma split_data_at_app_tschar:
 forall sh n (al bl: list val) p ,
   n = Zlength (al++bl) ->
   data_at sh (tarray tschar n) (al++bl) p = 
         data_at sh (tarray tschar (Zlength al)) al p
        * data_at sh (tarray tschar (n - Zlength al)) bl
                 (field_address0 (tarray tschar n) [ArraySubsc (Zlength al)] p).
Proof.
intros.
apply (split_data_at_app sh tschar n al bl (al++bl)); auto.
Qed.

Lemma body_strcpy: semax_body Vprog Gprog f_strcpy strcpy_spec.
Proof.
start_function.
unfold cstring,cstringn in *.
rename s into ls.
forward.
Intros.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength ls + 1)
  LOCAL (temp _i (Vint (Int.repr i)); temp _dest dest; temp _src src)
  SEP (data_at Tsh (tarray tschar n)
        (map Vbyte (sublist 0 i ls) ++ list_repeat (Z.to_nat (n - i)) Vundef) dest;
       data_at Tsh (tarray tschar (Zlength ls + 1)) (map Vbyte (ls ++ [Byte.zero])) src)).
*
 Exists 0. rewrite Z.sub_0_r; entailer!.
*
 Intros i.
 assert (Zlength (ls ++ [Byte.zero]) = Zlength ls + 1) by (autorewrite with sublist; auto).
 forward. normalize.
 forward. fold_Vbyte.
 forward.
 forward_if.
+ forward.
   entailer!.
  assert (i = Zlength ls) by cstring. subst i.
  change (field_at Tsh (tarray tschar n) []) with (data_at Tsh (tarray tschar n)).
  autorewrite with sublist.
  rewrite !map_app.
  rewrite <- app_assoc.
   rewrite (split_data_at_app_tschar _ n) by list_solve.
   rewrite (split_data_at_app_tschar _ n) by list_solve.
   autorewrite with sublist.
   replace (n - Zlength ls) with (1 + (n - (Zlength ls + 1))) at 2 by list_solve.
  rewrite <- list_repeat_app' by omega.
  autorewrite with sublist.
  rewrite !split_data_at_app_tschar by list_solve.
  cancel.
+
   assert (i < Zlength ls) by cstring.
  forward.
  forward.
  Exists (i+1). entailer!.
  rewrite upd_Znth_app2 by list_solve.
  assert (i < Zlength ls) by cstring.
  rewrite (sublist_split 0 i (i+1)) by list_solve.
  rewrite !map_app. rewrite <- app_assoc.
  autorewrite with sublist.
  change (field_at Tsh (tarray tschar n) []) with (data_at Tsh (tarray tschar n)).
  rewrite !(split_data_at_app_tschar _ n) by list_solve.
  autorewrite with sublist.
   replace (n - i) with (1 + (n-(i+ 1))) at 2 by list_solve.
  rewrite <- list_repeat_app' by omega.
  autorewrite with sublist.
  cancel.
  rewrite !split_data_at_app_tschar by list_solve.
  autorewrite with sublist.
  rewrite sublist_len_1 by omega.
  simpl. cancel.
Qed.

Lemma body_strcmp: semax_body Vprog Gprog f_strcmp strcmp_spec.
Proof.
start_function.
unfold cstring in *.
rename s1 into ls1. rename s2 into ls2.
forward.
Intros.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength ls1 + 1; 0 <= i < Zlength ls2 + 1;
        sublist 0 i ls1 = sublist 0 i ls2)
  LOCAL (temp _str1 str1; temp _str2 str2; temp _i (Vint (Int.repr i)))
  SEP (data_at Tsh (tarray tschar (Zlength ls1 + 1))
          (map Vbyte (ls1 ++ [Byte.zero])) str1;
       data_at Tsh (tarray tschar (Zlength ls2 + 1))
          (map Vbyte (ls2 ++ [Byte.zero])) str2)).
- Exists 0; entailer!.
- Intros i.
  assert (Zlength (ls1 ++ [Byte.zero]) = Zlength ls1 + 1) by (autorewrite with sublist; auto).
  forward. normalize.
  assert (Zlength (ls2 ++ [Byte.zero]) = Zlength ls2 + 1) by (autorewrite with sublist; auto).
  forward. fold_Vbyte.
  assert (Znth i (ls1 ++ [Byte.zero]) = Byte.zero <-> i = Zlength ls1) as Hs1.
  { split; [|intro; subst; rewrite app_Znth2, Zminus_diag by omega; auto].
    destruct (zlt i (Zlength ls1)); [|omega].
    intro X; lapply (Znth_In i ls1); [|omega]. cstring. }
  assert (Znth i (ls2 ++ [Byte.zero]) = Byte.zero <-> i = Zlength ls2) as Hs2.
  { split; [|intro; subst; rewrite app_Znth2, Zminus_diag by omega; auto].
    destruct (zlt i (Zlength ls2)); [|omega].
    intro X; lapply (Znth_In i ls2); [|omega]. cstring. }
  forward. normalize.
  forward. fold_Vbyte.
  forward_if (temp _t'1 (Val.of_bool (Z.eqb i (Zlength ls1) && Z.eqb i (Zlength ls2)))).
  { forward.
    simpl force_val. normalize.
    rewrite Hs1 in *.
    destruct (Byte.eq_dec (Znth i (ls2 ++ [Byte.zero])) Byte.zero).
    + rewrite e; simpl force_val.
         assert (i = Zlength ls2) by cstring.
        rewrite  (proj2 Hs1 H6).
     rewrite (proj2 (Z.eqb_eq i (Zlength ls1)) H6).
     rewrite (proj2 (Z.eqb_eq i (Zlength ls2)) H7).
     entailer!.
  +
    rewrite Int.eq_false.
     rewrite (proj2 (Z.eqb_eq i (Zlength ls1)) H6).
     rewrite Hs2 in n.
     rewrite (proj2 (Z.eqb_neq i (Zlength ls2))) by auto.
    entailer!.
     contradict n.
     apply repr_inj_signed in n; try rep_omega. normalize in n.
 }
  { forward.
    entailer!.
    destruct (i =? Zlength ls1) eqn: Heq; auto.
    rewrite Z.eqb_eq in Heq; tauto. }
  forward_if. 
 +
  rewrite andb_true_iff in H6; destruct H6.
  rewrite Z.eqb_eq in H6,H7.
  forward.
  Exists (Int.repr 0).
  entailer!. simpl.
  autorewrite with sublist in H3.
  auto.
 +
  rewrite andb_false_iff in H6. rewrite !Z.eqb_neq in H6.
  forward_if.
  *
    forward. Exists (Int.repr (-1)). entailer!.
    simpl. intro; subst. omega.
 *
   forward_if.
   forward.
   Exists (Int.repr 1). entailer!. simpl. intro. subst. omega.

   assert (H17: Byte.signed (Znth i (ls1 ++ [Byte.zero])) =
     Byte.signed (Znth i (ls2 ++ [Byte.zero]))) by omega.
   normalize in H17. clear H7 H8.
   forward.
   forward.
   Exists (i+1).
   entailer!.
   clear - H17 H6 Hs1 Hs2 H3 H1 H2 H H0.
   destruct (zlt i (Zlength ls1)).
  Focus 2. {
         assert (i = Zlength ls1) by omega. subst.
         destruct H6; [congruence | ].
         assert (Zlength ls1 < Zlength ls2) by omega.
         rewrite app_Znth2 in H17 by rep_omega.
         rewrite app_Znth1 in H17 by rep_omega.
         rewrite Z.sub_diag in H17. contradiction H0.
         change (Znth 0 [Byte.zero]) with Byte.zero in H17.
         rewrite H17. apply Znth_In. omega.
   } Unfocus.
  destruct (zlt i (Zlength ls2)).
  Focus 2. {
         assert (i = Zlength ls2) by omega. subst.
         destruct H6; [ | congruence].
         assert (Zlength ls1 > Zlength ls2) by omega.
         rewrite app_Znth1 in H17 by rep_omega.
         rewrite app_Znth2 in H17 by rep_omega.
         rewrite Z.sub_diag in H17. contradiction H.
         change (Znth 0 [Byte.zero]) with Byte.zero in H17.
         rewrite <- H17.  apply Znth_In. omega.
   } Unfocus.
  rewrite (sublist_split 0 i (i+1)) by omega.
  rewrite (sublist_split 0 i (i+1)) by omega.
  f_equal; auto.
  rewrite !sublist_len_1 by omega.
  autorewrite with sublist in H17.
  split. rep_omega. split. rep_omega.
  f_equal; auto. f_equal. auto.
Qed.
