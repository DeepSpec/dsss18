(*! Section ExternalTest *)

Typeclasses eauto := 3.

From Coq Require Import Basics String List ZArith.
From ExtLib Require Import
     Functor Traversable List OptionMonad StateMonad.
From QuickChick Require Import QuickChick.
From DeepWeb Require Import
     Test.Client
     Test.Rand
     Lib.Util
     Lib.SimpleSpec.

Import FunctorNotation ListNotations MonadNotation.
Open Scope program_scope.

Fixpoint filterSome {A} (l : list (option A)) : list A :=
  match l with
  | [] => []
  | Some a :: l => a :: filterSome l
  | None :: l => filterSome l
  end.

Definition recv_external (cid_fd : connection_id * file_descr) :
  IO (option event) :=
  let (cid, fd) := cid_fd in
  ob <- recvb fd;;
  ret (Event (ObsFromServer cid) ∘ Some <$> (ob : option byte)).

Definition Client := stateT (list (connection_id * file_descr)) IO.

Definition pick_error {A} (l : list A) : IO (option A) :=
  match l with
  | [] => ret None
  | a0::_ =>
    n <- rand (length l);;
    ret (Some (nth n l a0))
  end.

Definition pick {A} (l : list A) (a0 : A) : IO A :=
  oa <- pick_error l;;
  ret (match oa with
       | None => a0
       | Some a => a
       end).

Definition max_connections : nat := 4.

Definition newConnection : Client (option (connection_id * file_descr * trace)) :=
  lift (log ("new connection"));;
  connections <- get;;
  match connections with
  | [] =>
    ofd <- lift socket;;
    match ofd with
    | Some fd =>
      let c := (Connection 0, fd) in
      put [c];;
      ret (Some (c, [Event ObsConnect (Connection 0)]))
    | None => ret None
    end
  | c0::_ =>
    if length connections <? max_connections
    then
      ofd <- lift socket;;
      match ofd with
      | Some fd =>
        let c := (Connection (length connections), fd) in
        put (c :: connections);;
        ret (Some (c, [Event ObsConnect (fst c)]))
      | None => ret None
      end
    else ret (Some (c0, []))
  end.

Definition sendMessage
           (cid : connection_id)
           (fd : file_descr)
           (b : byte) : Client event :=
  lift (log ("sending " ++ show b));;
  lift (sendb fd b);;
  ret (Event (ObsToServer cid) b).

Definition recvMessages : Client trace :=
  l <- get;;
  lift (filterSome <$> mapT recv_external l).

Definition closeAll : Client (list unit) :=
  lift (log ("closing all connections"));;
  connections <- get;;
  put [];;
  mapT (lift ∘ close ∘ snd) connections.

Fixpoint execute' (fuel : nat) (msgs : list byte) : Client trace :=
  lift (log ("exec " ++ show fuel ++ " " ++ show msgs));;
  match fuel with
  | 0 =>
    lift (log "out of fuel, closing all connections");;
    closeAll;;
    ret []
  | S fuel =>
    match msgs with
    | [] =>
      lift (log ("nothing to send, receiving messages"));;
      connections <- get;;
      tr <- recvMessages;;
      lift (log ("received " ++ show tr));;
      closeAll;;
      ret tr
    | msg::msgs' =>
      connections <- get;;
      match connections with
      | [] =>
        lift (log "flip true, creating first connection");;
        ocft <- newConnection;;
        match ocft with
        | Some cft =>
          let (cf, tr) := cft in
          let cid := fst cf in
          lift (log ("created connection " ++ show cid));;
          tr' <- execute' fuel msgs;;
          ret (app tr tr')
        | None =>
          lift (log "failed to create connection, skipping");;
          execute' fuel msgs
        end
      | c0::_ =>
        b <- lift flip;;
        if b : bool
        then
          lift (log "flip true, sending messages");;
          n <- lift (rand (length connections));;
          let '(cid, fd) := nth n connections c0 in
          ev <- sendMessage cid fd msg;;
          lift (log ("sent " ++ show msg ++ " to " ++ show cid));;
          tr' <- execute' fuel msgs';;
          ret (ev::tr')
        else
          b <- lift flip;;
          if b : bool then
            lift (log "flip false-true, receiving messages");;
            connections <- get;;
            tr <- recvMessages;;
            lift (log ("received " ++ show tr));;
            tr' <- execute' fuel msgs;;
            ret (app tr tr')
          else
            lift (log "flip false-false, creating connection");;
            ocft <- newConnection;;
            match ocft with
            | Some (cid, _, tr) =>
              lift (log ("created connection " ++ show cid));;
              tr' <- execute' fuel msgs;;
              ret (app tr tr')
            | None =>
              lift (log "failed to create connection, skipping");;
              execute' fuel msgs
            end
      end
    end
  end.

Definition execute (msgs : list byte) : Client trace :=
  ret (log (nl ++ "Execute: "++ show msgs ++ nl));;
  tr <- execute' (S (length msgs) * 4) msgs;;
  ret (log (nl ++ "Trace: " ++ show tr ++ nl));;
  ret tr.

Instance Checkable_result : Checkable result :=
  {| checker r :=
       match r with
       | Found _ => checker true
       | NotFound => checker false
       | OutOfFuel => checker tt
       end |}.

Require DeepWeb.Spec.Swap_SimpleSpec.

Definition execute_prop (msgs : list byte) : Checker :=
  let tr := runIO_with_server (evalStateT (execute msgs) []) in
  whenFail (show tr)
           (is_scrambled_trace_of 100 (Swap_SimpleSpec.swap_spec_def) tr).

(*! QuickChick execute_prop. *)
