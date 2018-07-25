(* Conversion from the effects used in the VST part
   to the simplified version used by SimpleSpec. *)

From DeepWeb.Free.Monad Require Import
     Free Common Internal.
Import MonadNotations.
Import SumNotations.

From DeepWeb.Lib Require Import
     NetworkInterface
     SimpleSpec_Server.

Module N0 := NetworkInterface.Network.
Module N1 := SimpleSpec_Server.

Definition E0 := nondetE +' failureE +' N0.networkE.
Definition serverE1 := N1.ServerType.serverE.

Definition simplify_network' {E}
           `{failureE -< E} `{nondetE -< E} `{serverE1 -< E} :
  forall X, E0 X -> M E X :=
  fun _ e =>
    match e with
    | (| e ) =>
      match e in N0.networkE X return M E X with
      | N0.Listen _ => ret tt
      | N0.Accept _ => N1.accept
      | N0.RecvByte c => N1.recv_byte c
      | N0.SendByte c b => N1.send_byte c b
      | N0.Shutdown c => fail "not implemented"
      end
    | (| Fail reason |) => fail reason
    | ( _Or ||) => liftE (convert _Or)
    end.

Definition simplify_network {E}
           `{failureE -< E} `{nondetE -< E} `{serverE1 -< E} :
  forall X, M E0 X -> M E X :=
  fun _ => hom simplify_network'.

Arguments simplify_network {E _ _ _} [X].
