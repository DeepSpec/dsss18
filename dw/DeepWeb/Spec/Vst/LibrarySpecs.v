Require Import String.

From DeepWeb.Spec
     Require Import Vst.MainInit.

(********************************** Library ***********************************)

Definition memset_spec :=
  DECLARE _memset
  WITH ptr : val, v : Z, n : Z
  PRE [ 1%positive OF tptr tvoid,
        2%positive OF tint,
        3%positive OF tuint
      ]
    PROP ( 0 <= n <= Int.max_unsigned ) 
    LOCAL ( temp 1%positive ptr ;
              temp 2%positive (Vint (Int.repr v)) ;
              temp 3%positive (Vint (Int.repr n))
          )
    SEP ( data_at_ Tsh (tarray tuchar n) ptr )
  POST [ tptr tvoid ]
    PROP ( )
    LOCAL ( temp ret_temp ptr )
    SEP ( data_at Tsh (tarray tuchar n) 
                  (list_repeat (Z.to_nat n) (Vint (Int.repr v))) ptr
        ).

Definition memcpy_spec :=
  DECLARE _memcpy
  WITH contents : list val,
       dst_ptr : val,
       src_ptr : val,
       n : Z,
       sh : share
  PRE [ 1%positive OF tptr tvoid,
        2%positive OF tptr tvoid,
        3%positive OF tuint
      ]
    PROP ( 0 <= n <= Int.max_unsigned ) 
    LOCAL ( temp 1%positive dst_ptr ;
            temp 2%positive src_ptr;
            temp 3%positive (Vint (Int.repr n))
          )
    SEP ( data_at_ Tsh (tarray tuchar n) dst_ptr ;
          data_at sh (tarray tuchar n) contents src_ptr
        )
  POST [ tptr tvoid ]
    PROP ( )
    LOCAL ( temp ret_temp dst_ptr )
    SEP ( data_at Tsh (tarray tuchar n) contents dst_ptr ; 
          data_at sh (tarray tuchar n) contents src_ptr
        ).

Ltac forward_memcpy dst_ptr src_ptr len :=
  unfold tarray;
  match goal with
  | [|- context[data_at ?sh (Tarray tuchar ?n ?attr) ?contents src_ptr]] =>
    forward_call (contents, dst_ptr, src_ptr, n, sh)
  end.