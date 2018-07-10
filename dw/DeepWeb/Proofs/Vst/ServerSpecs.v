Require Import String.

From DeepWeb.Proofs.Vst
     Require Import VstInit VstLib SocketSpecs Connection Store
     MonadExports LibrarySpecs
     new_store_spec new_connection_spec reset_connection_spec
     populate_response_spec check_if_complete_spec
     accept_connection_spec conn_read_spec conn_write_spec
     process_spec add_to_fd_set_spec
     monitor_connections_spec process_connections_spec
     select_loop_spec.

Require Import DeepWeb.Spec.ITreeSpec.

Import SockAPIPred.
Import TracePred.
Import FDSetPred.
Import ITreeSpec.

Opaque list_repeat.
Opaque BUFFER_SIZE.

Open Scope logic.
Open Scope list.

Set Bullet Behavior "Strict Subproofs".

(******************************************************************************)


(******************************************************************************)

Definition main_spec :=
  DECLARE _main
  WITH gv : globals
  PRE [ _argc OF tint, _argv OF (tptr (tptr tschar)) ] (main_pre prog [] gv)
  POST [ tint ]
  PROP()
  LOCAL(temp ret_temp (Vint (Int.repr 0)))
  SEP(TT).

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [
            memset_spec;
            memcpy_spec;

            new_store_spec;
            check_if_complete_spec;
            populate_response_spec;  
            new_connection_spec;
            reset_connection_spec;
            accept_connection_spec unit;
            conn_read_spec unit;
            conn_write_spec unit;
            process_spec unit;
            monitor_connections_spec;
            process_connections_spec;
            select_loop_spec unit;
            add_to_fd_set_spec;

            accept_spec unit;
            recv_msg_spec unit;
            send_msg_spec unit;
            select_spec unit;
            close_spec unit;
            shutdown_spec unit;

            fd_zero_macro_spec;
            fd_set_macro_spec;
            fd_isset_macro_spec;

            main_spec
       ]).