Require Import String.

From DeepWeb.Proofs.Vst
     Require Import VstInit VstLib.

Set Bullet Behavior "Strict Subproofs".

Require Import DeepWeb.Spec.ITreeSpec.

(***************************** check_if_complete ******************************)

Definition check_if_complete_spec :=
  DECLARE _check_if_complete
  WITH msg : string,
       buf_ptr : val,
       msg_len : Z,
       sh : share
  PRE [ 1%positive OF tptr tuchar,
        2%positive OF tuint ] 
    PROP ( )
    LOCAL ( temp 1%positive buf_ptr ;
              temp 2%positive (Vint (Int.repr msg_len)))
    SEP ( data_at sh (tarray tuchar msg_len) (val_of_string msg) buf_ptr )
  POST [ tint ]
    EX r : Z, 
    PROP ( r = 1 \/ r = 0;
             r = 1 -> is_complete msg = true;
             r = 0 -> is_complete msg = false
         )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( data_at sh (tarray tuchar msg_len) (val_of_string msg) buf_ptr ).
