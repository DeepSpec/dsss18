type ('env, 'state) task  = 
  { fd : Unix.file_descr
  ; mutable select_on : bool
  ; mutable wake_time : float option
  ; mutable process_read : ('env, 'state) task -> 'env -> 'state -> bool * ('env, 'state) task list * 'state
  ; mutable process_wake : ('env, 'state) task -> 'env -> 'state -> bool * ('env, 'state) task list * 'state
  ; finalize : ('env, 'state) task -> 'env -> 'state -> 'state
  }

val schedule_finalize_task : ('env, 'state) task -> float -> unit

val eloop : float -> float -> (Unix.file_descr, ('env, 'state) task) Hashtbl.t -> 'env -> 'state -> unit
