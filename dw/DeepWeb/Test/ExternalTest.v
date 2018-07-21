(*! Section ExternalTest *)

Typeclasses eauto := 3.

From Coq Require Import Basics String List ZArith.
From ExtLib Require Import Functor OptionMonad StateMonad.
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

Definition recv_external (cid_fd : connection_id * file_descr) : option event :=
  let (cid, fd) := cid_fd in
  Event (ObsFromServer cid) ∘ Some <$> recvb fd.

Definition Client := state (list (connection_id * file_descr)).

Definition pick_error {A} (l : list A) : option A :=
  match l with
  | [] => None
  | a0::_ => Some (nth (rand (length l)) l a0)
  end.

Definition pick {A} (l : list A) (a0 : A) : A :=
  match pick_error l with
  | None => a0
  | Some a => a
  end.

Definition max_connections : nat := 4.

Definition newConnection : Client (option (connection_id * file_descr * trace)) :=
  ret (log ("new connection"));;
  connections <- get;;
  match connections with
  | [] =>
    match socket tt with
    | Some fd =>
      let c := (Connection 0, fd) in
      put [c];;
      ret (Some (c, [Event ObsConnect (Connection 0)]))
    | None => ret None
    end
  | c0::_ =>
    if length connections <? max_connections
    then
      match socket tt with
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
  ret (log ("sending " ++ show b));;
  ret (sendb fd b);;
  ret (Event (ObsToServer cid) b).

Definition recvMessage (l : list (connection_id * file_descr)) : trace :=
  filterSome (map recv_external l).

Definition closeAll : Client (list unit) :=
  ret (log ("closing all connections"));;
  connections <- get;;
  put [];;
  ret (map (close ∘ snd) connections).

Fixpoint execute' (fuel : nat) (msgs : list byte) : Client trace :=
  ret (log ("exec " ++ show fuel ++ " " ++ show msgs));;
  match fuel with
  | 0 => ret (log "out of fuel, closing all connections");;
        closeAll;;
        ret []
  | S fuel =>
    match msgs with
    | [] =>
      ret (log ("nothing to send, receiving messages"));;
      tr <- recvMessage <$> get;;
      ret (log ("received " ++ show tr));;
      closeAll;;
      ret tr
    | msg::msgs' =>
      if flip tt
      then
        connections <- get;;
        match connections with
        | [] =>
          ret (log "flip true, creating first connection");;
          ocft <- newConnection;;
          match ocft with
          | Some cft =>
            let (cf, tr) := cft in
            let cid := fst cf in
            ret (log ("created connection " ++ show cid));;
            tr' <- execute' fuel msgs;;
            ret (app tr tr')
          | None =>
            ret (log "failed to create connection, skipping");;
            execute' fuel msgs
          end
        | c0::_ =>
          ret (log "flip true, sending messages");;
          let c := nth (rand (length connections)) connections c0 in
          ev <- sendMessage (fst c) (snd c) msg;;
          ret (log ("sent " ++ show msg ++ " to " ++ show (fst c)));;
          tr' <- execute' fuel msgs';;
          ret (ev::tr')
        end
      else
        if flip tt
        then
          ret (log "flip false-true, receiving messages");;
          connections <- get;;
          tr <- ret (recvMessage connections);;
          ret (log ("received " ++ show tr));;
          tr' <- execute' fuel msgs;;
          ret (app tr tr')
        else
          ret (log "flip false-false, creating connection");;
          ocft <- newConnection;;
          match ocft with
          | Some cft =>
            let (cf, tr) := cft in
            let cid := fst cf in
            ret (log ("created connection " ++ show cid));;
            tr' <- execute' fuel msgs;;
            ret (app tr tr')
          | None =>
            ret (log "failed to create connection, skipping");;
            execute' fuel msgs
          end
    end
  end.

Definition execute (msgs : list byte) : Client trace :=
  ret (log (nl ++ "Execute: "++ show msgs ++ nl));;
  tr <- execute' (S (length msgs) * 4) (init msgs);;
  ret (log (nl ++ "Trace: " ++ show tr ++ nl));;
  stop <$> ret tr.

Instance Checkable_result : Checkable result :=
  {| checker r :=
       match r with
       | Found => checker true
       | NotFound => checker false
       | OutOfFuel => checker tt
       end |}.

Require DeepWeb.Spec.Swap_SimpleSpec.

Definition execute_prop (msgs : list byte) : Checker :=
  let tr := evalState (execute msgs) [] in
  whenFail (show tr)
  (is_scrambled_trace_of 100 (Swap_SimpleSpec.swap_spec_def) tr).

(* BCP: Once the external tests work, put the bang back! *)
(* QuickChick execute_prop. *)
