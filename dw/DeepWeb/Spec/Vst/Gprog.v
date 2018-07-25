From VST
     Require Import sepcomp.extspec veric.juicy_mem veric.semax_ext.

Require Import DeepWeb.Spec.Swap_CLikeSpec.

From DeepWeb.Spec.Vst
     Require Import MainInit SocketSpecs
     MonadExports LibrarySpecs
     zeroize_addr_spec bind_socket_spec new_store_spec init_store_spec
     new_connection_spec reset_connection_spec
     populate_response_spec check_if_complete_spec
     accept_connection_spec conn_read_spec conn_write_spec
     process_spec add_to_fd_set_spec
     monitor_connections_spec process_connections_spec
     select_loop_spec.


Import TracePred.
Import SockAPIPred.

Definition void_spec T : external_specification juicy_mem external_function T :=
    Build_external_specification
      juicy_mem external_function T
      (fun ef => False)
      (fun ef Hef ge tys vl m z => False)
      (fun ef Hef ge ty vl m z => False)
      (fun rv m z => False).

Definition ok_void_spec (T : Type) : OracleKind.
 refine (Build_OracleKind T (Build_juicy_ext_spec _ (void_spec T) _ _ _)).
Proof.
  simpl; intros; contradiction.
  simpl; intros; contradiction.
  simpl; intros; intros ? ? ? ?; contradiction.
Defined.

Definition ext_link := ext_link_prog main.prog.

Definition socket_ext_spec
  :=
  add_funspecs_rec
    ext_link
    (ok_void_spec (SocketM unit)).(@OK_ty)
    (ok_void_spec (SocketM unit)).(@OK_spec)
    socket_specs.

Instance Socket_Espec : OracleKind :=
  Build_OracleKind
    (SocketM unit)
    (socket_ext_spec).

Definition main_spec (tree : SocketM unit) :=
  DECLARE _main
  WITH gv : globals
  PRE [ ]
  (PROP ( )
   LOCAL (gvars gv)
   SEP (SOCKAPI {| lookup_socket := fun _ : sockfd => ClosedSocket |} ;
        ITREE tree))
  POST [ tint ]
  PROP ( False )
  LOCAL ( temp ret_temp (Vint (Int.repr 0)) )
  SEP ( ).

Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* Packaging the API spec all together. *)

Definition specs :=
  socket_specs
    ++
    [  memset_spec;
       memcpy_spec;

       fd_zero_macro_spec;
       fd_set_macro_spec;
       fd_isset_macro_spec;
       htons_spec;

       zeroize_addr_spec;
       bind_socket_spec;
       new_store_spec;
       init_store_spec;
       check_if_complete_spec BUFFER_SIZE;
       populate_response_spec;  
       new_connection_spec;
       reset_connection_spec;
       accept_connection_spec unit;
       conn_read_spec unit BUFFER_SIZE;
       conn_write_spec unit BUFFER_SIZE;
       process_spec unit BUFFER_SIZE;
       monitor_connections_spec;
       process_connections_spec BUFFER_SIZE;
       select_loop_spec;
       add_to_fd_set_spec; 
       
       main_spec server
    ].

Definition Gprog : funspecs :=
  ltac:(with_library prog specs).

Instance Espec : OracleKind :=
  add_funspecs Socket_Espec (ext_link_prog prog) Gprog.

Axiom body_fd_zero_macro:
  semax_body Vprog Gprog f_fd_zero_macro fd_zero_macro_spec.

Axiom body_fd_set_macro:
  semax_body Vprog Gprog f_fd_set_macro fd_set_macro_spec.

Axiom body_fd_isset_macro:
  semax_body Vprog Gprog f_fd_isset_macro fd_isset_macro_spec.

Axiom body_zeroize_addr:
  semax_body Vprog Gprog f_zeroize_addr zeroize_addr_spec.
