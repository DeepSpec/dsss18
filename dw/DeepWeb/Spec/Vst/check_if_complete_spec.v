Require Import String.

From DeepWeb.Spec
     Require Import Vst.MainInit Swap_CLikeSpec.

From DeepWeb.Lib
     Require Import VstLib.

Set Bullet Behavior "Strict Subproofs".

(***************************** check_if_complete ******************************)

Definition check_if_complete_spec (buffer_size : Z) :=
  DECLARE _check_if_complete
  WITH msg : string,
       buf_ptr : val,
       msg_len : Z,
       sh : share
  PRE [ _buffer_ptr OF tptr tuchar,
        _len OF tuint ] 
    PROP ( 0 <= msg_len <= Int.max_signed )
    LOCAL ( temp _buffer_ptr buf_ptr ;
            temp _len (Vint (Int.repr msg_len)))
    SEP ( data_at sh (tarray tuchar msg_len) (val_of_string msg) buf_ptr )
  POST [ tint ]
    EX r : Z, 
    PROP ( r = 1 \/ r = 0;
             r = 1 -> is_complete buffer_size msg = true;
             r = 0 -> is_complete buffer_size msg = false
         )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( data_at sh (tarray tuchar msg_len) (val_of_string msg) buf_ptr ).
