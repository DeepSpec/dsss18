Require Import String.

From DeepWeb.Proofs.Vst
     Require Import VstInit Store.

Set Bullet Behavior "Strict Subproofs".

Definition new_store_spec :=
  DECLARE _new_store
  WITH tt : unit
  PRE [] 
    PROP ()
    LOCAL ()
    SEP ()
  POST [ (tptr (Tstruct _store noattr)) ]
    EX store_opt : option store,
    EX r : val, 
    PROP ( isptr r \/ r = nullval ;
             isptr r ->
             store_opt = Some {| stored_msg := "" |}; 
             r = nullval -> store_opt = None
         )
    LOCAL ( temp ret_temp r )
    SEP ( match store_opt with
          | Some store =>
            malloc_token Tsh (Tstruct _store noattr) r *
            field_at Tsh (Tstruct _store noattr) [] (rep_store "") r
          | None => emp
          end
        ).