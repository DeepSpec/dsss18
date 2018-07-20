Require Import DeepWeb.Spec.Swap_CLikeSpec.

From DeepWeb.Spec.Vst
     Require Import MainInit SocketSpecs main_spec
     MonadExports LibrarySpecs
     zeroize_addr_spec bind_socket_spec new_store_spec init_store_spec
     new_connection_spec reset_connection_spec
     populate_response_spec check_if_complete_spec
     accept_connection_spec conn_read_spec conn_write_spec
     process_spec add_to_fd_set_spec
     monitor_connections_spec process_connections_spec
     select_loop_spec.

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