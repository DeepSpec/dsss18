Typeclasses eauto := 3.

From Coq Require Import Basics List ZArith.
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

Definition newConnection : Client (connection_id * file_descr) :=
  connections <- get;;
  let c := (Connection (length connections), socket tt) in
  put (c :: connections);;
  ret c.

Definition sendMessage (b : byte) : Client event :=
  connections <- get;;
  match connections with
  | [] => c <- newConnection;;
         ret (sendb (snd c) b);;
         ret (Event (ObsToServer (fst c)) b)
  | c0::_ =>
    let c := nth (rand (length connections)) connections c0 in
    ret (sendb (snd c) b);;
    ret (Event (ObsToServer (fst c)) b)
  end.

Definition recvMessage (l : list (connection_id * file_descr)) : trace :=
  filterSome (map recv_external l).

Definition closeAll : Client (list unit) :=
  connections <- get;;
  put [];;
  ret (map (close ∘ snd) connections).

Fixpoint execute' (fuel : nat) (msgs : list byte) : Client trace :=
  match fuel with
  | 0 => closeAll;;
        ret []
  | S fuel =>
    match msgs with
    | [] =>
      tr <- recvMessage <$> get;;
      closeAll;;
      ret tr
    | msg::msgs' =>
      if flip tt
      then
        ev <- sendMessage msg;;
        evs <- execute' fuel msgs';;
        ret (ev::evs)
      else
        if flip tt
        then
          connections <- get;;
          evs <- execute' fuel msgs;;
          ret ((recvMessage connections) ++ evs)
        else
          newConnection;;
          execute' fuel msgs
    end
  end.

Definition execute (msgs : list byte) : Client trace :=
  init <$> execute' (length msgs * 3) msgs.

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
  (is_scrambled_trace_of 1000 (Swap_SimpleSpec.swap_spec_def) tr).

(*! QuickChick execute_prop. *)
