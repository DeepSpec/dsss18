Require Import String.

From DeepWeb.Spec.Vst
     Require Import MainInit.

Require Import DeepWeb.Lib.VstLib.

Open Scope logic.
Open Scope list.

Lemma field_at_rep_store_eq:
  forall (sh : share) (ptr : val) (msg_rep : list val) (msg_len_rep : val)
    (store_rep : val * list val),
    store_rep = (msg_len_rep, msg_rep) ->
    field_at sh (Tstruct _store noattr) [] store_rep ptr
    = field_at sh (Tstruct _store noattr)
               [StructField _stored_msg_len] msg_len_rep ptr
      * field_at sh (Tstruct _store noattr)
                 [StructField _stored_msg]
                 msg_rep ptr.
Proof.
  intros.
  erewrite field_at_Tstruct; [| reflexivity | apply (JMeq_refl _)].
  simpl.
  subst.
  unfold withspacer.
  simpl; reflexivity.
Qed.
