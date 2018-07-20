Require Import String.

From DeepWeb.Spec
     Require Import Vst.MainInit Vst.Representation ServerDefs.

Definition init_store_spec :=
  DECLARE _init_store
  WITH ptr : val
  PRE [ _last_msg_store OF tptr (Tstruct _store noattr) ] 
    PROP ()
    LOCAL ( temp _last_msg_store ptr )
    SEP ( field_at Tsh (Tstruct _store noattr) [] (rep_store "") ptr )
  POST [ tvoid ]
    PROP ( )
    LOCAL ( )
    SEP ( field_at Tsh (Tstruct _store noattr) [] (rep_store INIT_MSG) ptr ).