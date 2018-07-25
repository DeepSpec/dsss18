(* Check that the interfaces defined in [Lib.SimpleSpec]
   are actually implemented by the modules actually
   exported by [Lib.SimpleSpec]. *)

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.

Require Import DeepWeb.Lib.Util.

From DeepWeb Require Import
     Lib.SimpleSpec_Server
     Lib.SimpleSpec_Observer
     Lib.SimpleSpec_Descramble
     Lib.SimpleSpec_Traces
     Lib.SimpleSpec_Refinement
     Lib.SimpleSpec_ServerTrace
     Lib.SimpleSpec_NetworkModel
     Lib.SimpleSpec.

Module Network <: ServerIface.
Include Lib.SimpleSpec_Server.ServerType.
Definition E := failureE +' nondetE +' serverE.
Definition ServerM := M E.
Definition accept := @accept E _.
Definition recv_byte := @recv_byte E _.
Definition send_byte := @send_byte E _.
Definition recv := @recv E _ _.
Definition recv_full := @recv_full E _.
Definition send := @send E _.
End Network.

Module Observer <: ObserverIface.
Include Lib.SimpleSpec_Observer.ObserverType.
Definition E := failureE +' nondetE +' observerE.
Definition ObserverM := ObserverM.
Definition obs_connect := @obs_connect E _.
Definition obs_to_server := @obs_to_server E _.
Definition obs_from_server := @obs_from_server E _.
Definition assert_on A := @assert_on E A _ _.
Definition obs_msg_to_server := @obs_msg_to_server E _.
Definition obs_msg_from_server := @obs_msg_from_server E _ _ _.
End Observer.

Module Traces <: TracesIface.
  Include SimpleSpec_Traces.
  Definition is_server_trace := SimpleSpec_Server.is_server_trace.
  Definition is_observer_trace := SimpleSpec_Observer.is_observer_trace.
  Definition is_observer_trace_test := SimpleSpec_Observer.is_observer_trace_test.
End Traces.

Module NetworkModel <: NetworkModelIface.
  Include SimpleSpec_NetworkModel.
End NetworkModel.

Module Descrambling <: DescramblingIface Traces NetworkModel.
  Include Traces.

  Definition is_scrambled_trace
    := SimpleSpec_Observer.is_scrambled_trace.
  Definition refines_mod_network
    := SimpleSpec_Refinement.refines_mod_network.

  Definition descrambled_result := Lib.Util.result hypo_trace unit.
  Definition is_scrambled_trace_test
    := SimpleSpec_Descramble.is_scrambled_trace_test.
  Definition refines_mod_network_test
    := SimpleSpec_ServerTrace.refines_mod_network_test.
End Descrambling.
