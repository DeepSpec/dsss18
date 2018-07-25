From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Definition _fd_set : ident := 15%positive.
Definition ___arr : ident := 95%positive.
Definition ___builtin_annot : ident := 34%positive.
Definition ___builtin_annot_intval : ident := 35%positive.
Definition ___builtin_bswap : ident := 28%positive.
Definition ___builtin_bswap16 : ident := 30%positive.
Definition ___builtin_bswap32 : ident := 29%positive.
Definition ___builtin_bswap64 : ident := 60%positive.
Definition ___builtin_clz : ident := 61%positive.
Definition ___builtin_clzl : ident := 62%positive.
Definition ___builtin_clzll : ident := 63%positive.
Definition ___builtin_ctz : ident := 64%positive.
Definition ___builtin_ctzl : ident := 65%positive.
Definition ___builtin_ctzll : ident := 66%positive.
Definition ___builtin_debug : ident := 78%positive.
Definition ___builtin_fabs : ident := 31%positive.
Definition ___builtin_fmadd : ident := 69%positive.
Definition ___builtin_fmax : ident := 67%positive.
Definition ___builtin_fmin : ident := 68%positive.
Definition ___builtin_fmsub : ident := 70%positive.
Definition ___builtin_fnmadd : ident := 71%positive.
Definition ___builtin_fnmsub : ident := 72%positive.
Definition ___builtin_fsqrt : ident := 32%positive.
Definition ___builtin_membar : ident := 36%positive.
Definition ___builtin_memcpy_aligned : ident := 33%positive.
Definition ___builtin_nop : ident := 77%positive.
Definition ___builtin_read16_reversed : ident := 73%positive.
Definition ___builtin_read32_reversed : ident := 74%positive.
Definition ___builtin_va_arg : ident := 38%positive.
Definition ___builtin_va_copy : ident := 39%positive.
Definition ___builtin_va_end : ident := 40%positive.
Definition ___builtin_va_start : ident := 37%positive.
Definition ___builtin_write16_reversed : ident := 75%positive.
Definition ___builtin_write32_reversed : ident := 76%positive.
Definition ___compcert_i64_dtos : ident := 45%positive.
Definition ___compcert_i64_dtou : ident := 46%positive.
Definition ___compcert_i64_sar : ident := 57%positive.
Definition ___compcert_i64_sdiv : ident := 51%positive.
Definition ___compcert_i64_shl : ident := 55%positive.
Definition ___compcert_i64_shr : ident := 56%positive.
Definition ___compcert_i64_smod : ident := 53%positive.
Definition ___compcert_i64_smulh : ident := 58%positive.
Definition ___compcert_i64_stod : ident := 47%positive.
Definition ___compcert_i64_stof : ident := 49%positive.
Definition ___compcert_i64_udiv : ident := 52%positive.
Definition ___compcert_i64_umod : ident := 54%positive.
Definition ___compcert_i64_umulh : ident := 59%positive.
Definition ___compcert_i64_utod : ident := 48%positive.
Definition ___compcert_i64_utof : ident := 50%positive.
Definition ___compcert_va_composite : ident := 44%positive.
Definition ___compcert_va_float64 : ident := 43%positive.
Definition ___compcert_va_int32 : ident := 41%positive.
Definition ___compcert_va_int64 : ident := 42%positive.
Definition ___fds_bits : ident := 14%positive.
Definition ___i : ident := 94%positive.
Definition _accept : ident := 89%positive.
Definition _accept_connection : ident := 128%positive.
Definition _add_to_fd_set : ident := 131%positive.
Definition _addr : ident := 149%positive.
Definition _addr_len : ident := 152%positive.
Definition _bind : ident := 85%positive.
Definition _bind_socket : ident := 153%positive.
Definition _buffer : ident := 104%positive.
Definition _buffer_ptr : ident := 99%positive.
Definition _check_if_complete : ident := 101%positive.
Definition _close : ident := 83%positive.
Definition _complete : ident := 115%positive.
Definition _conn : ident := 106%positive.
Definition _conn_fd : ident := 112%positive.
Definition _conn_read : ident := 117%positive.
Definition _conn_st : ident := 123%positive.
Definition _conn_write : ident := 122%positive.
Definition _connection : ident := 23%positive.
Definition _curr : ident := 134%positive.
Definition _curr_fd : ident := 136%positive.
Definition _curr_st : ident := 135%positive.
Definition _es : ident := 143%positive.
Definition _exit : ident := 80%positive.
Definition _fd : ident := 16%positive.
Definition _fd_isset_macro : ident := 97%positive.
Definition _fd_set_macro : ident := 98%positive.
Definition _fd_zero_macro : ident := 96%positive.
Definition _head : ident := 126%positive.
Definition _htons : ident := 91%positive.
Definition _in_addr : ident := 5%positive.
Definition _init_store : ident := 154%positive.
Definition _last_msg : ident := 108%positive.
Definition _last_msg_len : ident := 109%positive.
Definition _last_msg_store : ident := 107%positive.
Definition _len : ident := 100%positive.
Definition _listen : ident := 88%positive.
Definition _main : ident := 155%positive.
Definition _malloc : ident := 79%positive.
Definition _max_fd : ident := 129%positive.
Definition _maxsock : ident := 145%positive.
Definition _memcpy : ident := 81%positive.
Definition _memset : ident := 82%positive.
Definition _monitor_connections : ident := 137%positive.
Definition _new_connection : ident := 103%positive.
Definition _new_len : ident := 114%positive.
Definition _new_store : ident := 105%positive.
Definition _next : ident := 24%positive.
Definition _num_bytes_sent : ident := 21%positive.
Definition _num_bytes_to_send : ident := 121%positive.
Definition _num_ready : ident := 147%positive.
Definition _old_head : ident := 127%positive.
Definition _populate_response : ident := 110%positive.
Definition _port : ident := 151%positive.
Definition _process : ident := 124%positive.
Definition _process_connections : ident := 141%positive.
Definition _ptr : ident := 113%positive.
Definition _r : ident := 111%positive.
Definition _read_socket_ready : ident := 139%positive.
Definition _recv : ident := 87%positive.
Definition _request : ident := 118%positive.
Definition _request_buffer : ident := 18%positive.
Definition _request_len : ident := 17%positive.
Definition _reset_connection : ident := 120%positive.
Definition _response : ident := 119%positive.
Definition _response_buffer : ident := 20%positive.
Definition _response_len : ident := 19%positive.
Definition _response_ok : ident := 116%positive.
Definition _result : ident := 102%positive.
Definition _rs : ident := 132%positive.
Definition _s_addr : ident := 4%positive.
Definition _sa_data : ident := 2%positive.
Definition _sa_family : ident := 1%positive.
Definition _select : ident := 92%positive.
Definition _select_loop : ident := 148%positive.
Definition _send : ident := 86%positive.
Definition _server_socket : ident := 142%positive.
Definition _set : ident := 93%positive.
Definition _shutdown : ident := 90%positive.
Definition _sin_addr : ident := 8%positive.
Definition _sin_family : ident := 6%positive.
Definition _sin_port : ident := 7%positive.
Definition _sin_zero : ident := 9%positive.
Definition _sockaddr : ident := 3%positive.
Definition _sockaddr_in : ident := 10%positive.
Definition _socket : ident := 84%positive.
Definition _socket__1 : ident := 125%positive.
Definition _socket_ready : ident := 138%positive.
Definition _st : ident := 22%positive.
Definition _store : ident := 27%positive.
Definition _stored_msg : ident := 26%positive.
Definition _stored_msg_len : ident := 25%positive.
Definition _timeout : ident := 144%positive.
Definition _timeval : ident := 13%positive.
Definition _tmp : ident := 130%positive.
Definition _tmp_head : ident := 146%positive.
Definition _tv_sec : ident := 11%positive.
Definition _tv_usec : ident := 12%positive.
Definition _write_socket_ready : ident := 140%positive.
Definition _ws : ident := 133%positive.
Definition _zeroize_addr : ident := 150%positive.
Definition _t'1 : ident := 156%positive.
Definition _t'2 : ident := 157%positive.
Definition _t'3 : ident := 158%positive.
Definition _t'4 : ident := 159%positive.

Definition f_fd_zero_macro := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_set, (tptr (Tstruct _fd_set noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((___i, tuint) :: (___arr, (tptr (Tstruct _fd_set noattr))) ::
               nil);
  fn_body :=
(Sloop
  (Ssequence
    (Sset ___arr (Etempvar _set (tptr (Tstruct _fd_set noattr))))
    (Ssequence
      (Sset ___i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar ___i tuint)
                         (Ebinop Odiv (Esizeof (Tstruct _fd_set noattr) tuint)
                           (Esizeof tint tuint) tuint) tint)
            Sskip
            Sbreak)
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar ___arr (tptr (Tstruct _fd_set noattr)))
                    (Tstruct _fd_set noattr)) ___fds_bits (tarray tint 32))
                (Etempvar ___i tuint) (tptr tint)) tint)
            (Econst_int (Int.repr 0) tint)))
        (Sset ___i
          (Ebinop Oadd (Etempvar ___i tuint) (Econst_int (Int.repr 1) tint)
            tuint)))))
  Sbreak)
|}.

Definition f_fd_isset_macro := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_fd, tint) :: (_set, (tptr (Tstruct _fd_set noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop One
                 (Ebinop Oand
                   (Ederef
                     (Ebinop Oadd
                       (Efield
                         (Ederef
                           (Etempvar _set (tptr (Tstruct _fd_set noattr)))
                           (Tstruct _fd_set noattr)) ___fds_bits
                         (tarray tint 32))
                       (Ebinop Odiv (Etempvar _fd tint)
                         (Ebinop Omul (Econst_int (Int.repr 8) tint)
                           (Ecast (Esizeof tint tuint) tint) tint) tint)
                       (tptr tint)) tint)
                   (Ecast
                     (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                       (Ebinop Omod (Etempvar _fd tint)
                         (Ebinop Omul (Econst_int (Int.repr 8) tint)
                           (Ecast (Esizeof tint tuint) tint) tint) tint)
                       tuint) tint) tint) (Econst_int (Int.repr 0) tint)
                 tint)))
|}.

Definition f_fd_set_macro := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fd, tint) :: (_set, (tptr (Tstruct _fd_set noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Ecast
      (Ebinop Oor
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _set (tptr (Tstruct _fd_set noattr)))
                (Tstruct _fd_set noattr)) ___fds_bits (tarray tint 32))
            (Ebinop Odiv (Etempvar _fd tint)
              (Ebinop Omul (Econst_int (Int.repr 8) tint)
                (Ecast (Esizeof tint tuint) tint) tint) tint) (tptr tint))
          tint)
        (Ecast
          (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
            (Ebinop Omod (Etempvar _fd tint)
              (Ebinop Omul (Econst_int (Int.repr 8) tint)
                (Ecast (Esizeof tint tuint) tint) tint) tint) tuint) tint)
        tint) tint))
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _set (tptr (Tstruct _fd_set noattr)))
            (Tstruct _fd_set noattr)) ___fds_bits (tarray tint 32))
        (Ebinop Odiv (Etempvar _fd tint)
          (Ebinop Omul (Econst_int (Int.repr 8) tint)
            (Ecast (Esizeof tint tuint) tint) tint) tint) (tptr tint)) tint)
    (Etempvar _t'1 tint)))
|}.

Definition f_check_if_complete := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_buffer_ptr, (tptr tuchar)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Econst_int (Int.repr 1024) tint)
                 (Etempvar _len tuint) tint)
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
    Sskip)
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_new_connection := {|
  fn_return := (tptr (Tstruct _connection noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _connection noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _connection noattr) tuint) :: nil))
    (Sset _result
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _connection noattr)))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _result (tptr (Tstruct _connection noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Etempvar _result (tptr (Tstruct _connection noattr)))))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _result (tptr (Tstruct _connection noattr)))
            (Tstruct _connection noattr)) _fd tint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _result (tptr (Tstruct _connection noattr)))
              (Tstruct _connection noattr)) _request_len tuint)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _result (tptr (Tstruct _connection noattr)))
                (Tstruct _connection noattr)) _response_len tuint)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _result (tptr (Tstruct _connection noattr)))
                  (Tstruct _connection noattr)) _num_bytes_sent tuint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _result (tptr (Tstruct _connection noattr)))
                    (Tstruct _connection noattr)) _st tint)
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _result (tptr (Tstruct _connection noattr)))
                      (Tstruct _connection noattr)) _next
                    (tptr (Tstruct _connection noattr)))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                (Sreturn (Some (Etempvar _result (tptr (Tstruct _connection noattr)))))))))))))
|}.

Definition f_new_store := {|
  fn_return := (tptr (Tstruct _store noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _store noattr))) ::
               (_buffer, (tptr tuchar)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _store noattr) tuint) :: nil))
    (Sset _result
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _store noattr)))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _result (tptr (Tstruct _store noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Etempvar _result (tptr (Tstruct _store noattr)))))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _result (tptr (Tstruct _store noattr)))
            (Tstruct _store noattr)) _stored_msg_len tuint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sset _buffer
          (Efield
            (Ederef (Etempvar _result (tptr (Tstruct _store noattr)))
              (Tstruct _store noattr)) _stored_msg (tarray tuchar 1024)))
        (Ssequence
          (Scall None
            (Evar _memset (Tfunction
                            (Tcons (tptr tvoid)
                              (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
                            cc_default))
            ((Etempvar _buffer (tptr tuchar)) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 1024) tint) :: nil))
          (Sreturn (Some (Etempvar _result (tptr (Tstruct _store noattr))))))))))
|}.

Definition f_populate_response := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_conn, (tptr (Tstruct _connection noattr))) ::
                (_last_msg_store, (tptr (Tstruct _store noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_last_msg, (tptr tuchar)) :: (_last_msg_len, tuint) ::
               (_response_buffer, (tptr tuchar)) :: (_request_len, tuint) ::
               (_request_buffer, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _last_msg
    (Efield
      (Ederef (Etempvar _last_msg_store (tptr (Tstruct _store noattr)))
        (Tstruct _store noattr)) _stored_msg (tarray tuchar 1024)))
  (Ssequence
    (Sset _last_msg_len
      (Efield
        (Ederef (Etempvar _last_msg_store (tptr (Tstruct _store noattr)))
          (Tstruct _store noattr)) _stored_msg_len tuint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
            (Tstruct _connection noattr)) _num_bytes_sent tuint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
              (Tstruct _connection noattr)) _response_len tuint)
          (Etempvar _last_msg_len tuint))
        (Ssequence
          (Sset _response_buffer
            (Efield
              (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
                (Tstruct _connection noattr)) _response_buffer
              (tarray tuchar 1024)))
          (Ssequence
            (Scall None
              (Evar _memcpy (Tfunction
                              (Tcons (tptr tvoid)
                                (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                              (tptr tvoid) cc_default))
              ((Etempvar _response_buffer (tptr tuchar)) ::
               (Etempvar _last_msg (tptr tuchar)) ::
               (Etempvar _last_msg_len tuint) :: nil))
            (Ssequence
              (Sset _request_len
                (Efield
                  (Ederef
                    (Etempvar _conn (tptr (Tstruct _connection noattr)))
                    (Tstruct _connection noattr)) _request_len tuint))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _last_msg_store (tptr (Tstruct _store noattr)))
                      (Tstruct _store noattr)) _stored_msg_len tuint)
                  (Etempvar _request_len tuint))
                (Ssequence
                  (Sset _request_buffer
                    (Efield
                      (Ederef
                        (Etempvar _conn (tptr (Tstruct _connection noattr)))
                        (Tstruct _connection noattr)) _request_buffer
                      (tarray tuchar 1024)))
                  (Ssequence
                    (Scall None
                      (Evar _memcpy (Tfunction
                                      (Tcons (tptr tvoid)
                                        (Tcons (tptr tvoid)
                                          (Tcons tuint Tnil))) (tptr tvoid)
                                      cc_default))
                      ((Etempvar _last_msg (tptr tuchar)) ::
                       (Etempvar _request_buffer (tptr tuchar)) ::
                       (Etempvar _request_len tuint) :: nil))
                    (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))))))))
|}.

Definition f_conn_read := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_conn, (tptr (Tstruct _connection noattr))) ::
                (_last_msg_store, (tptr (Tstruct _store noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, tint) :: (_conn_fd, tint) :: (_request_len, tuint) ::
               (_request_buffer, (tptr tuchar)) :: (_ptr, (tptr tuchar)) ::
               (_new_len, tuint) :: (_complete, tint) ::
               (_response_ok, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _conn_fd
    (Efield
      (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
        (Tstruct _connection noattr)) _fd tint))
  (Ssequence
    (Sset _request_len
      (Efield
        (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
          (Tstruct _connection noattr)) _request_len tuint))
    (Ssequence
      (Sset _request_buffer
        (Efield
          (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
            (Tstruct _connection noattr)) _request_buffer
          (tarray tuchar 1024)))
      (Ssequence
        (Sset _ptr
          (Ebinop Oadd (Etempvar _request_buffer (tptr tuchar))
            (Etempvar _request_len tuint) (tptr tuchar)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _recv (Tfunction
                            (Tcons tint
                              (Tcons (tptr tvoid)
                                (Tcons tuint (Tcons tint Tnil)))) tint
                            cc_default))
              ((Etempvar _conn_fd tint) :: (Etempvar _ptr (tptr tuchar)) ::
               (Ebinop Osub (Econst_int (Int.repr 1024) tint)
                 (Etempvar _request_len tuint) tuint) ::
               (Econst_int (Int.repr 0) tint) :: nil))
            (Sset _r (Etempvar _t'1 tint)))
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _r tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              Sskip)
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _r tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _conn (tptr (Tstruct _connection noattr)))
                        (Tstruct _connection noattr)) _st tint)
                    (Econst_int (Int.repr 3) tint))
                  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                Sskip)
              (Ssequence
                (Sset _new_len
                  (Ebinop Oadd (Etempvar _request_len tuint)
                    (Etempvar _r tint) tuint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _conn (tptr (Tstruct _connection noattr)))
                        (Tstruct _connection noattr)) _request_len tuint)
                    (Etempvar _new_len tuint))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'2)
                        (Evar _check_if_complete (Tfunction
                                                   (Tcons (tptr tuchar)
                                                     (Tcons tuint Tnil)) tint
                                                   cc_default))
                        ((Etempvar _request_buffer (tptr tuchar)) ::
                         (Etempvar _new_len tuint) :: nil))
                      (Sset _complete (Etempvar _t'2 tint)))
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _complete tint)
                                     (Econst_int (Int.repr 0) tint) tint)
                        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                        Sskip)
                      (Ssequence
                        (Sset _response_ok (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'3)
                              (Evar _populate_response (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _connection noattr))
                                                           (Tcons
                                                             (tptr (Tstruct _store noattr))
                                                             Tnil)) tint
                                                         cc_default))
                              ((Etempvar _conn (tptr (Tstruct _connection noattr))) ::
                               (Etempvar _last_msg_store (tptr (Tstruct _store noattr))) ::
                               nil))
                            (Sset _response_ok (Etempvar _t'3 tint)))
                          (Ssequence
                            (Sifthenelse (Ebinop Oeq
                                           (Etempvar _response_ok tint)
                                           (Econst_int (Int.repr 0) tint)
                                           tint)
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _conn (tptr (Tstruct _connection noattr)))
                                      (Tstruct _connection noattr)) _st tint)
                                  (Econst_int (Int.repr 3) tint))
                                (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                              Sskip)
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _conn (tptr (Tstruct _connection noattr)))
                                    (Tstruct _connection noattr)) _st tint)
                                (Econst_int (Int.repr 1) tint))
                              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))))
|}.

Definition f_reset_connection := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_conn, (tptr (Tstruct _connection noattr))) ::
                (_fd, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_request, (tptr tuchar)) :: (_response, (tptr tuchar)) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _request
    (Efield
      (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
        (Tstruct _connection noattr)) _request_buffer (tarray tuchar 1024)))
  (Ssequence
    (Sset _response
      (Efield
        (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
          (Tstruct _connection noattr)) _response_buffer
        (tarray tuchar 1024)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
            (Tstruct _connection noattr)) _fd tint) (Etempvar _fd tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
              (Tstruct _connection noattr)) _st tint)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
                (Tstruct _connection noattr)) _response_len tuint)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
                  (Tstruct _connection noattr)) _num_bytes_sent tuint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _conn (tptr (Tstruct _connection noattr)))
                    (Tstruct _connection noattr)) _request_len tuint)
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Scall None
                  (Evar _memset (Tfunction
                                  (Tcons (tptr tvoid)
                                    (Tcons tint (Tcons tuint Tnil)))
                                  (tptr tvoid) cc_default))
                  ((Etempvar _request (tptr tuchar)) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 1024) tint) :: nil))
                (Scall None
                  (Evar _memset (Tfunction
                                  (Tcons (tptr tvoid)
                                    (Tcons tint (Tcons tuint Tnil)))
                                  (tptr tvoid) cc_default))
                  ((Etempvar _response (tptr tuchar)) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 1024) tint) :: nil))))))))))
|}.

Definition f_conn_write := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_conn, (tptr (Tstruct _connection noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, tint) :: (_conn_fd, tint) :: (_response_len, tuint) ::
               (_num_bytes_sent, tuint) :: (_response, (tptr tuchar)) ::
               (_num_bytes_to_send, tuint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _conn_fd
    (Efield
      (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
        (Tstruct _connection noattr)) _fd tint))
  (Ssequence
    (Sset _response_len
      (Efield
        (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
          (Tstruct _connection noattr)) _response_len tuint))
    (Ssequence
      (Sset _num_bytes_sent
        (Efield
          (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
            (Tstruct _connection noattr)) _num_bytes_sent tuint))
      (Ssequence
        (Sset _response
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
                (Tstruct _connection noattr)) _response_buffer
              (tarray tuchar 1024)) (Etempvar _num_bytes_sent tuint)
            (tptr tuchar)))
        (Ssequence
          (Sset _num_bytes_to_send
            (Ebinop Osub (Etempvar _response_len tuint)
              (Etempvar _num_bytes_sent tuint) tuint))
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _send (Tfunction
                              (Tcons tint
                                (Tcons (tptr tvoid)
                                  (Tcons tuint (Tcons tint Tnil)))) tint
                              cc_default))
                ((Etempvar _conn_fd tint) ::
                 (Etempvar _response (tptr tuchar)) ::
                 (Etempvar _num_bytes_to_send tuint) ::
                 (Econst_int (Int.repr 0) tint) :: nil))
              (Sset _r (Etempvar _t'1 tint)))
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _r tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _conn (tptr (Tstruct _connection noattr)))
                        (Tstruct _connection noattr)) _st tint)
                    (Econst_int (Int.repr 3) tint))
                  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                Sskip)
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _conn (tptr (Tstruct _connection noattr)))
                      (Tstruct _connection noattr)) _num_bytes_sent tuint)
                  (Ebinop Oadd (Etempvar _num_bytes_sent tuint)
                    (Etempvar _r tint) tuint))
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _r tint)
                                 (Etempvar _num_bytes_to_send tuint) tint)
                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                    Sskip)
                  (Ssequence
                    (Scall None
                      (Evar _reset_connection (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _connection noattr))
                                                  (Tcons tint Tnil)) tvoid
                                                cc_default))
                      ((Etempvar _conn (tptr (Tstruct _connection noattr))) ::
                       (Etempvar _conn_fd tint) :: nil))
                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))
|}.

Definition f_process := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_conn, (tptr (Tstruct _connection noattr))) ::
                (_last_msg_store, (tptr (Tstruct _store noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, tint) :: (_conn_st, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _conn_st
    (Efield
      (Ederef (Etempvar _conn (tptr (Tstruct _connection noattr)))
        (Tstruct _connection noattr)) _st tint))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _conn_st tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Scall (Some _t'1)
          (Evar _conn_read (Tfunction
                             (Tcons (tptr (Tstruct _connection noattr))
                               (Tcons (tptr (Tstruct _store noattr)) Tnil))
                             tint cc_default))
          ((Etempvar _conn (tptr (Tstruct _connection noattr))) ::
           (Etempvar _last_msg_store (tptr (Tstruct _store noattr))) :: nil))
        (Sreturn (Some (Etempvar _t'1 tint))))
      Sskip)
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _conn_st tint)
                     (Econst_int (Int.repr 1) tint) tint)
        (Ssequence
          (Scall (Some _t'2)
            (Evar _conn_write (Tfunction
                                (Tcons (tptr (Tstruct _connection noattr))
                                  Tnil) tint cc_default))
            ((Etempvar _conn (tptr (Tstruct _connection noattr))) :: nil))
          (Sreturn (Some (Etempvar _t'2 tint))))
        Sskip)
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_accept_connection := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_socket__1, tint) ::
                (_head, (tptr (tptr (Tstruct _connection noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_fd, tint) :: (_conn, (tptr (Tstruct _connection noattr))) ::
               (_old_head, (tptr (Tstruct _connection noattr))) ::
               (_t'2, (tptr (Tstruct _connection noattr))) :: (_t'1, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _accept (Tfunction
                      (Tcons tint
                        (Tcons (tptr (Tstruct _sockaddr noattr))
                          (Tcons (tptr tuint) Tnil))) tint cc_default))
      ((Etempvar _socket__1 tint) ::
       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil))
    (Sset _fd (Etempvar _t'1 tint)))
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _fd tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
      Sskip)
    (Ssequence
      (Sifthenelse (Ebinop Oge (Etempvar _fd tint)
                     (Econst_int (Int.repr 1024) tint) tint)
        (Ssequence
          (Scall None
            (Evar _shutdown (Tfunction (Tcons tint (Tcons tint Tnil)) tint
                              cc_default))
            ((Etempvar _fd tint) :: (Econst_int (Int.repr 2) tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _close (Tfunction (Tcons tint Tnil) tint cc_default))
              ((Etempvar _fd tint) :: nil))
            (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))))
        Sskip)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _new_connection (Tfunction Tnil
                                    (tptr (Tstruct _connection noattr))
                                    cc_default)) nil)
          (Sset _conn (Etempvar _t'2 (tptr (Tstruct _connection noattr)))))
        (Ssequence
          (Sifthenelse (Ebinop Oeq
                         (Etempvar _conn (tptr (Tstruct _connection noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Ssequence
              (Scall None
                (Evar _shutdown (Tfunction (Tcons tint (Tcons tint Tnil))
                                  tint cc_default))
                ((Etempvar _fd tint) :: (Econst_int (Int.repr 2) tint) ::
                 nil))
              (Ssequence
                (Scall None
                  (Evar _close (Tfunction (Tcons tint Tnil) tint cc_default))
                  ((Etempvar _fd tint) :: nil))
                (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                 tint)))))
            Sskip)
          (Ssequence
            (Scall None
              (Evar _reset_connection (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _connection noattr))
                                          (Tcons tint Tnil)) tvoid
                                        cc_default))
              ((Etempvar _conn (tptr (Tstruct _connection noattr))) ::
               (Etempvar _fd tint) :: nil))
            (Ssequence
              (Sset _old_head
                (Ederef
                  (Etempvar _head (tptr (tptr (Tstruct _connection noattr))))
                  (tptr (Tstruct _connection noattr))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _conn (tptr (Tstruct _connection noattr)))
                      (Tstruct _connection noattr)) _next
                    (tptr (Tstruct _connection noattr)))
                  (Etempvar _old_head (tptr (Tstruct _connection noattr))))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Etempvar _head (tptr (tptr (Tstruct _connection noattr))))
                      (tptr (Tstruct _connection noattr)))
                    (Etempvar _conn (tptr (Tstruct _connection noattr))))
                  (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))
|}.

Definition f_add_to_fd_set := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_fd, tint) :: (_set, (tptr (Tstruct _fd_set noattr))) ::
                (_max_fd, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_tmp, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _set (tptr (Tstruct _fd_set noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop Oge (Etempvar _fd tint)
                   (Econst_int (Int.repr 1024) tint) tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
      Sskip)
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _fd tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
        Sskip)
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _max_fd (tptr tint))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
          Sskip)
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _fd tint)
                         (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                         tint)
            (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
            Sskip)
          (Ssequence
            (Scall None
              (Evar _fd_set_macro (Tfunction
                                    (Tcons tint
                                      (Tcons (tptr (Tstruct _fd_set noattr))
                                        Tnil)) tvoid cc_default))
              ((Etempvar _fd tint) ::
               (Etempvar _set (tptr (Tstruct _fd_set noattr))) :: nil))
            (Ssequence
              (Sset _tmp (Ederef (Etempvar _max_fd (tptr tint)) tint))
              (Ssequence
                (Sifthenelse (Ebinop Ogt (Etempvar _fd tint)
                               (Etempvar _tmp tint) tint)
                  (Sassign (Ederef (Etempvar _max_fd (tptr tint)) tint)
                    (Etempvar _fd tint))
                  Sskip)
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))
|}.

Definition f_monitor_connections := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_head, (tptr (Tstruct _connection noattr))) ::
                (_rs, (tptr (Tstruct _fd_set noattr))) ::
                (_ws, (tptr (Tstruct _fd_set noattr))) ::
                (_max_fd, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_curr, (tptr (Tstruct _connection noattr))) ::
               (_curr_st, tint) :: (_curr_fd, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _curr (Etempvar _head (tptr (Tstruct _connection noattr))))
  (Swhile
    (Ebinop One (Etempvar _curr (tptr (Tstruct _connection noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Sset _curr_st
        (Efield
          (Ederef (Etempvar _curr (tptr (Tstruct _connection noattr)))
            (Tstruct _connection noattr)) _st tint))
      (Ssequence
        (Sset _curr_fd
          (Efield
            (Ederef (Etempvar _curr (tptr (Tstruct _connection noattr)))
              (Tstruct _connection noattr)) _fd tint))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _curr_st tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Scall None
              (Evar _add_to_fd_set (Tfunction
                                     (Tcons tint
                                       (Tcons (tptr (Tstruct _fd_set noattr))
                                         (Tcons (tptr tint) Tnil))) tint
                                     cc_default))
              ((Etempvar _curr_fd tint) ::
               (Etempvar _rs (tptr (Tstruct _fd_set noattr))) ::
               (Etempvar _max_fd (tptr tint)) :: nil))
            Sskip)
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _curr_st tint)
                           (Econst_int (Int.repr 1) tint) tint)
              (Scall None
                (Evar _add_to_fd_set (Tfunction
                                       (Tcons tint
                                         (Tcons
                                           (tptr (Tstruct _fd_set noattr))
                                           (Tcons (tptr tint) Tnil))) tint
                                       cc_default))
                ((Etempvar _curr_fd tint) ::
                 (Etempvar _ws (tptr (Tstruct _fd_set noattr))) ::
                 (Etempvar _max_fd (tptr tint)) :: nil))
              Sskip)
            (Sset _curr
              (Efield
                (Ederef (Etempvar _curr (tptr (Tstruct _connection noattr)))
                  (Tstruct _connection noattr)) _next
                (tptr (Tstruct _connection noattr))))))))))
|}.

Definition f_process_connections := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_head, (tptr (Tstruct _connection noattr))) ::
                (_rs, (tptr (Tstruct _fd_set noattr))) ::
                (_ws, (tptr (Tstruct _fd_set noattr))) ::
                (_last_msg_store, (tptr (Tstruct _store noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_socket_ready, tint) ::
               (_curr, (tptr (Tstruct _connection noattr))) ::
               (_curr_st, tint) :: (_curr_fd, tint) ::
               (_read_socket_ready, tint) :: (_write_socket_ready, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _curr (Etempvar _head (tptr (Tstruct _connection noattr))))
  (Swhile
    (Ebinop One (Etempvar _curr (tptr (Tstruct _connection noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Sset _curr_fd
        (Efield
          (Ederef (Etempvar _curr (tptr (Tstruct _connection noattr)))
            (Tstruct _connection noattr)) _fd tint))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _fd_isset_macro (Tfunction
                                    (Tcons tint
                                      (Tcons (tptr (Tstruct _fd_set noattr))
                                        Tnil)) tint cc_default))
            ((Etempvar _curr_fd tint) ::
             (Etempvar _rs (tptr (Tstruct _fd_set noattr))) :: nil))
          (Sset _read_socket_ready (Etempvar _t'1 tint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _fd_isset_macro (Tfunction
                                      (Tcons tint
                                        (Tcons (tptr (Tstruct _fd_set noattr))
                                          Tnil)) tint cc_default))
              ((Etempvar _curr_fd tint) ::
               (Etempvar _ws (tptr (Tstruct _fd_set noattr))) :: nil))
            (Sset _write_socket_ready (Etempvar _t'2 tint)))
          (Ssequence
            (Sset _socket_ready (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sifthenelse (Etempvar _read_socket_ready tint)
                (Sset _socket_ready (Econst_int (Int.repr 1) tint))
                (Sifthenelse (Etempvar _write_socket_ready tint)
                  (Sset _socket_ready (Econst_int (Int.repr 1) tint))
                  Sskip))
              (Ssequence
                (Sifthenelse (Ebinop Ogt (Etempvar _socket_ready tint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Scall None
                    (Evar _process (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _connection noattr))
                                       (Tcons (tptr (Tstruct _store noattr))
                                         Tnil)) tint cc_default))
                    ((Etempvar _curr (tptr (Tstruct _connection noattr))) ::
                     (Etempvar _last_msg_store (tptr (Tstruct _store noattr))) ::
                     nil))
                  Sskip)
                (Sset _curr
                  (Efield
                    (Ederef
                      (Etempvar _curr (tptr (Tstruct _connection noattr)))
                      (Tstruct _connection noattr)) _next
                    (tptr (Tstruct _connection noattr))))))))))))
|}.

Definition f_select_loop := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_server_socket, tint) ::
                (_last_msg_store, (tptr (Tstruct _store noattr))) :: nil);
  fn_vars := ((_rs, (Tstruct _fd_set noattr)) ::
              (_ws, (Tstruct _fd_set noattr)) ::
              (_es, (Tstruct _fd_set noattr)) ::
              (_timeout, (Tstruct _timeval noattr)) ::
              (_head, (tptr (Tstruct _connection noattr))) ::
              (_maxsock, tint) :: nil);
  fn_temps := ((_tmp_head, (tptr (Tstruct _connection noattr))) ::
               (_tmp, tint) :: (_num_ready, tint) :: (_socket_ready, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _head (tptr (Tstruct _connection noattr)))
    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sassign (Evar _maxsock tint)
      (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
    (Ssequence
      (Sassign
        (Efield (Evar _timeout (Tstruct _timeval noattr)) _tv_sec tint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield (Evar _timeout (Tstruct _timeval noattr)) _tv_usec tint)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign (Evar _head (tptr (Tstruct _connection noattr)))
            (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
          (Ssequence
            (Swhile
              (Ebinop Oeq (Econst_int (Int.repr 1) tint)
                (Econst_int (Int.repr 1) tint) tint)
              (Ssequence
                (Scall None
                  (Evar _fd_zero_macro (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _fd_set noattr))
                                           Tnil) tvoid cc_default))
                  ((Eaddrof (Evar _rs (Tstruct _fd_set noattr))
                     (tptr (Tstruct _fd_set noattr))) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _fd_zero_macro (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _fd_set noattr))
                                             Tnil) tvoid cc_default))
                    ((Eaddrof (Evar _ws (Tstruct _fd_set noattr))
                       (tptr (Tstruct _fd_set noattr))) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _fd_zero_macro (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _fd_set noattr))
                                               Tnil) tvoid cc_default))
                      ((Eaddrof (Evar _es (Tstruct _fd_set noattr))
                         (tptr (Tstruct _fd_set noattr))) :: nil))
                    (Ssequence
                      (Sassign (Evar _maxsock tint)
                        (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                      (Ssequence
                        (Scall None
                          (Evar _add_to_fd_set (Tfunction
                                                 (Tcons tint
                                                   (Tcons
                                                     (tptr (Tstruct _fd_set noattr))
                                                     (Tcons (tptr tint) Tnil)))
                                                 tint cc_default))
                          ((Etempvar _server_socket tint) ::
                           (Eaddrof (Evar _rs (Tstruct _fd_set noattr))
                             (tptr (Tstruct _fd_set noattr))) ::
                           (Eaddrof (Evar _maxsock tint) (tptr tint)) :: nil))
                        (Ssequence
                          (Sset _tmp_head
                            (Evar _head (tptr (Tstruct _connection noattr))))
                          (Ssequence
                            (Scall None
                              (Evar _monitor_connections (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _connection noattr))
                                                             (Tcons
                                                               (tptr (Tstruct _fd_set noattr))
                                                               (Tcons
                                                                 (tptr (Tstruct _fd_set noattr))
                                                                 (Tcons
                                                                   (tptr tint)
                                                                   Tnil))))
                                                           tvoid cc_default))
                              ((Etempvar _tmp_head (tptr (Tstruct _connection noattr))) ::
                               (Eaddrof (Evar _rs (Tstruct _fd_set noattr))
                                 (tptr (Tstruct _fd_set noattr))) ::
                               (Eaddrof (Evar _ws (Tstruct _fd_set noattr))
                                 (tptr (Tstruct _fd_set noattr))) ::
                               (Eaddrof (Evar _maxsock tint) (tptr tint)) ::
                               nil))
                            (Ssequence
                              (Sset _tmp (Evar _maxsock tint))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'1)
                                    (Evar _select (Tfunction
                                                    (Tcons tint
                                                      (Tcons
                                                        (tptr (Tstruct _fd_set noattr))
                                                        (Tcons
                                                          (tptr (Tstruct _fd_set noattr))
                                                          (Tcons
                                                            (tptr (Tstruct _fd_set noattr))
                                                            (Tcons
                                                              (tptr (Tstruct _timeval noattr))
                                                              Tnil))))) tint
                                                    cc_default))
                                    ((Ebinop Oadd (Etempvar _tmp tint)
                                       (Econst_int (Int.repr 1) tint) tint) ::
                                     (Eaddrof
                                       (Evar _rs (Tstruct _fd_set noattr))
                                       (tptr (Tstruct _fd_set noattr))) ::
                                     (Eaddrof
                                       (Evar _ws (Tstruct _fd_set noattr))
                                       (tptr (Tstruct _fd_set noattr))) ::
                                     (Eaddrof
                                       (Evar _es (Tstruct _fd_set noattr))
                                       (tptr (Tstruct _fd_set noattr))) ::
                                     (Eaddrof
                                       (Evar _timeout (Tstruct _timeval noattr))
                                       (tptr (Tstruct _timeval noattr))) ::
                                     nil))
                                  (Sset _num_ready (Etempvar _t'1 tint)))
                                (Ssequence
                                  (Sifthenelse (Ebinop Ole
                                                 (Etempvar _num_ready tint)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    Scontinue
                                    Sskip)
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'2)
                                        (Evar _fd_isset_macro (Tfunction
                                                                (Tcons tint
                                                                  (Tcons
                                                                    (tptr (Tstruct _fd_set noattr))
                                                                    Tnil))
                                                                tint
                                                                cc_default))
                                        ((Etempvar _server_socket tint) ::
                                         (Eaddrof
                                           (Evar _rs (Tstruct _fd_set noattr))
                                           (tptr (Tstruct _fd_set noattr))) ::
                                         nil))
                                      (Sset _socket_ready
                                        (Etempvar _t'2 tint)))
                                    (Ssequence
                                      (Sifthenelse (Etempvar _socket_ready tint)
                                        (Scall None
                                          (Evar _accept_connection (Tfunction
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr (tptr (Tstruct _connection noattr)))
                                                                    Tnil))
                                                                    tint
                                                                    cc_default))
                                          ((Etempvar _server_socket tint) ::
                                           (Eaddrof
                                             (Evar _head (tptr (Tstruct _connection noattr)))
                                             (tptr (tptr (Tstruct _connection noattr)))) ::
                                           nil))
                                        Sskip)
                                      (Ssequence
                                        (Sset _tmp_head
                                          (Evar _head (tptr (Tstruct _connection noattr))))
                                        (Scall None
                                          (Evar _process_connections 
                                          (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _connection noattr))
                                              (Tcons
                                                (tptr (Tstruct _fd_set noattr))
                                                (Tcons
                                                  (tptr (Tstruct _fd_set noattr))
                                                  (Tcons
                                                    (tptr (Tstruct _store noattr))
                                                    Tnil)))) tvoid
                                            cc_default))
                                          ((Etempvar _tmp_head (tptr (Tstruct _connection noattr))) ::
                                           (Eaddrof
                                             (Evar _rs (Tstruct _fd_set noattr))
                                             (tptr (Tstruct _fd_set noattr))) ::
                                           (Eaddrof
                                             (Evar _ws (Tstruct _fd_set noattr))
                                             (tptr (Tstruct _fd_set noattr))) ::
                                           (Etempvar _last_msg_store (tptr (Tstruct _store noattr))) ::
                                           nil))))))))))))))))
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))
|}.

Definition f_zeroize_addr := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_addr, (tptr (Tstruct _sockaddr_in noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _memset (Tfunction
                  (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                  (tptr tvoid) cc_default))
  ((Etempvar _addr (tptr (Tstruct _sockaddr_in noattr))) ::
   (Econst_int (Int.repr 0) tint) ::
   (Esizeof (Tstruct _sockaddr_in noattr) tuint) :: nil))
|}.

Definition f_bind_socket := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_fd, tint) :: (_port, tint) :: nil);
  fn_vars := ((_addr, (Tstruct _sockaddr_in noattr)) :: nil);
  fn_temps := ((_addr_len, tint) :: (_r, tint) :: (_t'2, tint) ::
               (_t'1, tushort) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _zeroize_addr (Tfunction
                          (Tcons (tptr (Tstruct _sockaddr_in noattr)) Tnil)
                          tvoid cc_default))
    ((Eaddrof (Evar _addr (Tstruct _sockaddr_in noattr))
       (tptr (Tstruct _sockaddr_in noattr))) :: nil))
  (Ssequence
    (Sset _addr_len (Esizeof (Tstruct _sockaddr_in noattr) tuint))
    (Ssequence
      (Sassign
        (Efield (Evar _addr (Tstruct _sockaddr_in noattr)) _sin_family
          tushort) (Econst_int (Int.repr 2) tint))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _htons (Tfunction (Tcons tushort Tnil) tushort cc_default))
            ((Etempvar _port tint) :: nil))
          (Sassign
            (Efield (Evar _addr (Tstruct _sockaddr_in noattr)) _sin_port
              tushort) (Etempvar _t'1 tushort)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _bind (Tfunction
                            (Tcons tint
                              (Tcons (tptr (Tstruct _sockaddr noattr))
                                (Tcons tuint Tnil))) tint cc_default))
              ((Etempvar _fd tint) ::
               (Ecast
                 (Eaddrof (Evar _addr (Tstruct _sockaddr_in noattr))
                   (tptr (Tstruct _sockaddr_in noattr)))
                 (tptr (Tstruct _sockaddr noattr))) ::
               (Etempvar _addr_len tint) :: nil))
            (Sset _r (Etempvar _t'2 tint)))
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _r tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
              Sskip)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))
|}.

Definition f_init_store := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_last_msg_store, (tptr (Tstruct _store noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_last_msg, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _last_msg_store (tptr (Tstruct _store noattr)))
        (Tstruct _store noattr)) _stored_msg_len tuint)
    (Econst_int (Int.repr 1024) tint))
  (Ssequence
    (Sset _last_msg
      (Ecast
        (Efield
          (Ederef (Etempvar _last_msg_store (tptr (Tstruct _store noattr)))
            (Tstruct _store noattr)) _stored_msg (tarray tuchar 1024))
        (tptr tschar)))
    (Scall None
      (Evar _memset (Tfunction
                      (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                      (tptr tvoid) cc_default))
      ((Etempvar _last_msg (tptr tschar)) ::
       (Econst_int (Int.repr 48) tint) ::
       (Econst_int (Int.repr 1024) tint) :: nil))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_fd, tint) :: (_r, tint) ::
               (_last_msg_store, (tptr (Tstruct _store noattr))) ::
               (_port, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, (tptr (Tstruct _store noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _new_store (Tfunction Tnil (tptr (Tstruct _store noattr))
                           cc_default)) nil)
      (Sset _last_msg_store (Etempvar _t'1 (tptr (Tstruct _store noattr)))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Etempvar _last_msg_store (tptr (Tstruct _store noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Scall None
          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 0) tint) :: nil))
        Sskip)
      (Ssequence
        (Scall None
          (Evar _init_store (Tfunction
                              (Tcons (tptr (Tstruct _store noattr)) Tnil)
                              tvoid cc_default))
          ((Etempvar _last_msg_store (tptr (Tstruct _store noattr))) :: nil))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _socket (Tfunction
                              (Tcons tint (Tcons tint (Tcons tint Tnil)))
                              tint cc_default))
              ((Econst_int (Int.repr 2) tint) ::
               (Econst_int (Int.repr 1) tint) ::
               (Econst_int (Int.repr 0) tint) :: nil))
            (Sset _fd (Etempvar _t'2 tint)))
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _fd tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Scall None
                (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
                ((Econst_int (Int.repr 0) tint) :: nil))
              Sskip)
            (Ssequence
              (Sifthenelse (Ebinop Oge (Etempvar _fd tint)
                             (Econst_int (Int.repr 1024) tint) tint)
                (Scall None
                  (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
                  ((Econst_int (Int.repr 0) tint) :: nil))
                Sskip)
              (Ssequence
                (Sset _port (Econst_int (Int.repr 8000) tint))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _bind_socket (Tfunction
                                           (Tcons tint (Tcons tint Tnil))
                                           tint cc_default))
                      ((Etempvar _fd tint) :: (Etempvar _port tint) :: nil))
                    (Sset _r (Etempvar _t'3 tint)))
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _r tint)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Scall None
                        (Evar _exit (Tfunction (Tcons tint Tnil) tvoid
                                      cc_default))
                        ((Econst_int (Int.repr 0) tint) :: nil))
                      Sskip)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'4)
                          (Evar _listen (Tfunction
                                          (Tcons tint (Tcons tint Tnil)) tint
                                          cc_default))
                          ((Etempvar _fd tint) ::
                           (Econst_int (Int.repr 128) tint) :: nil))
                        (Sset _r (Etempvar _t'4 tint)))
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _r tint)
                                       (Econst_int (Int.repr 0) tint) tint)
                          (Scall None
                            (Evar _exit (Tfunction (Tcons tint Tnil) tvoid
                                          cc_default))
                            ((Econst_int (Int.repr 0) tint) :: nil))
                          Sskip)
                        (Scall None
                          (Evar _select_loop (Tfunction
                                               (Tcons tint
                                                 (Tcons
                                                   (tptr (Tstruct _store noattr))
                                                   Tnil)) tint cc_default))
                          ((Etempvar _fd tint) ::
                           (Etempvar _last_msg_store (tptr (Tstruct _store noattr))) ::
                           nil)))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _sockaddr Struct
   ((_sa_family, tushort) :: (_sa_data, (tarray tschar 14)) :: nil)
   noattr :: Composite _in_addr Struct ((_s_addr, tuint) :: nil) noattr ::
 Composite _sockaddr_in Struct
   ((_sin_family, tushort) :: (_sin_port, tushort) ::
    (_sin_addr, (Tstruct _in_addr noattr)) ::
    (_sin_zero, (tarray tuchar 8)) :: nil)
   noattr ::
 Composite _timeval Struct
   ((_tv_sec, tint) :: (_tv_usec, tint) :: nil)
   noattr ::
 Composite _fd_set Struct ((___fds_bits, (tarray tint 32)) :: nil) noattr ::
 Composite _connection Struct
   ((_fd, tint) :: (_request_len, tuint) ::
    (_request_buffer, (tarray tuchar 1024)) :: (_response_len, tuint) ::
    (_response_buffer, (tarray tuchar 1024)) :: (_num_bytes_sent, tuint) ::
    (_st, tint) :: (_next, (tptr (Tstruct _connection noattr))) :: nil)
   noattr ::
 Composite _store Struct
   ((_stored_msg_len, tuint) :: (_stored_msg, (tarray tuchar 1024)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
     (tptr tvoid) cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
     cc_default)) ::
 (_close,
   Gfun(External (EF_external "close"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tint Tnil) tint cc_default)) ::
 (_socket,
   Gfun(External (EF_external "socket"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default)) ::
 (_bind,
   Gfun(External (EF_external "bind"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons tint
       (Tcons (tptr (Tstruct _sockaddr noattr)) (Tcons tuint Tnil))) tint
     cc_default)) ::
 (_send,
   Gfun(External (EF_external "send"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons tint (Tcons (tptr tvoid) (Tcons tuint (Tcons tint Tnil)))) tint
     cc_default)) ::
 (_recv,
   Gfun(External (EF_external "recv"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons tint (Tcons (tptr tvoid) (Tcons tuint (Tcons tint Tnil)))) tint
     cc_default)) ::
 (_listen,
   Gfun(External (EF_external "listen"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tint (Tcons tint Tnil)) tint
     cc_default)) ::
 (_accept,
   Gfun(External (EF_external "accept"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons tint
       (Tcons (tptr (Tstruct _sockaddr noattr)) (Tcons (tptr tuint) Tnil)))
     tint cc_default)) ::
 (_shutdown,
   Gfun(External (EF_external "shutdown"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tint (Tcons tint Tnil)) tint
     cc_default)) ::
 (_htons,
   Gfun(External (EF_external "htons"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (_select,
   Gfun(External (EF_external "select"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tint
       (Tcons (tptr (Tstruct _fd_set noattr))
         (Tcons (tptr (Tstruct _fd_set noattr))
           (Tcons (tptr (Tstruct _fd_set noattr))
             (Tcons (tptr (Tstruct _timeval noattr)) Tnil))))) tint
     cc_default)) :: (_fd_zero_macro, Gfun(Internal f_fd_zero_macro)) ::
 (_fd_isset_macro, Gfun(Internal f_fd_isset_macro)) ::
 (_fd_set_macro, Gfun(Internal f_fd_set_macro)) ::
 (_check_if_complete, Gfun(Internal f_check_if_complete)) ::
 (_new_connection, Gfun(Internal f_new_connection)) ::
 (_new_store, Gfun(Internal f_new_store)) ::
 (_populate_response, Gfun(Internal f_populate_response)) ::
 (_conn_read, Gfun(Internal f_conn_read)) ::
 (_reset_connection, Gfun(Internal f_reset_connection)) ::
 (_conn_write, Gfun(Internal f_conn_write)) ::
 (_process, Gfun(Internal f_process)) ::
 (_accept_connection, Gfun(Internal f_accept_connection)) ::
 (_add_to_fd_set, Gfun(Internal f_add_to_fd_set)) ::
 (_monitor_connections, Gfun(Internal f_monitor_connections)) ::
 (_process_connections, Gfun(Internal f_process_connections)) ::
 (_select_loop, Gfun(Internal f_select_loop)) ::
 (_zeroize_addr, Gfun(Internal f_zeroize_addr)) ::
 (_bind_socket, Gfun(Internal f_bind_socket)) ::
 (_init_store, Gfun(Internal f_init_store)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _select_loop :: _fd_set_macro :: _fd_isset_macro ::
 _fd_zero_macro :: _select :: _htons :: _shutdown :: _accept :: _listen ::
 _recv :: _send :: _bind :: _socket :: _close :: _memset :: _memcpy ::
 _exit :: _malloc :: ___builtin_debug :: ___builtin_nop ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_memcpy_aligned :: ___builtin_fsqrt :: ___builtin_fabs ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


