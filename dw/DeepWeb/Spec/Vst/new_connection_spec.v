Require Import String.

From DeepWeb.Spec
     Require Import Vst.MainInit Vst.SocketSpecs Vst.Representation
     Swap_CLikeSpec.

Require Import DeepWeb.Lib.VstLib.

Definition new_connection_spec :=
  DECLARE _new_connection
  WITH tt : unit
  PRE [] 
    PROP ()
    LOCAL ()
    SEP ()
  POST [ (tptr (Tstruct _connection noattr)) ]
    EX conn_opt : option connection,
    EX r : val, 
    PROP ( isptr r \/ r = nullval ;
             isptr r ->
             (conn_opt = Some {| conn_id := Connection 0%nat; (* dummy *)
                                 conn_request := "";
                                 conn_response := "";
                                 conn_response_bytes_sent := 0;
                                 conn_state := RECVING
                              |})
             ;
             r = nullval -> conn_opt = None
         )
    LOCAL ( temp ret_temp r )
    SEP (
      let zero_fd := {| descriptor := 0; is_descriptor := zero_is_fd |} in
      match conn_opt with
      | Some conn =>
        malloc_token Tsh (Tstruct _connection noattr) r *
        lseg LS Tsh Tsh
             ([(r, rep_connection conn zero_fd)])
             r nullval
      | None => emp
      end
    ).
