Require Import List.
Import ListNotations.
Require Import Omega.
Require Import FunctionalExtensionality.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import SimpleDS.SysDef.
Require Import SimpleDS.NetSem.
Require Import SimpleDS.SeqNum.

Module SeqNumProof (OrigSys : SystemParams).
  Module WrapSys := SeqNum(OrigSys).
  
  Module OrigSem := NetSem(OrigSys).
  Module WrapSem := NetSem(WrapSys).


  (* This is what we want to prove, to ensure that there
     are no "extra behaviors", but it's not inductive!

        forall ww,
          WrapSem.reachable WrapSem.dup_step ww ->
          exists ow,
            OrigSem.reachable OrigSem.shuffle_step ow /\
            OrigSem.trace ow = WrapSem.trace ww
   *)

  
  Ltac unpack_ws_handler :=
      unfold WrapSys.handle_input,
             WrapSys.handle_msg,
             WrapSys.do,
             WrapSys.nop,
             WrapSys.bind,
             WrapSys.ret,
             WrapSys.get,
             WrapSys.set in *;
      repeat break_let; repeat tuple_inversion.

  Ltac unfold_sem :=
      unfold WrapSem.update,
             WrapSem.locals,
             WrapSem.net,
             WrapSem.trace,
             OrigSem.update,
             OrigSem.locals,
             OrigSem.net,
             OrigSem.trace in *.

              
  (* which packets have already been delivered in ww, but linger in net *)
  Definition delivered (ww : WrapSem.world) (p : WrapSys.packet) : bool :=
    WrapSys.SNB.seen
      (WrapSem.locals ww (WrapSys.dest p))
      (WrapSys.SNB.src (WrapSys.payload p))
      (WrapSys.SNB.uid (WrapSys.payload p)).
  Opaque delivered.

  Definition undelivered_net (ww : WrapSem.world) : list WrapSys.packet :=
    List.filter
      (fun p => negb (delivered ww p))
      (WrapSem.net ww).

  Definition revert_packet (p : WrapSys.packet) : OrigSys.packet :=
    OrigSys.mkpacket
      (WrapSys.dest p)
      (WrapSys.SNB.orig_msg (WrapSys.payload p)).

  (* EXERCISE :
       Formalize and prove the fact that delivered packets stay
       delivered.  That is, if a packet p is delivered in some
       world ww, and ww steps to ww', then p is still delivered. 
   *)

  (* EXERCISE :
       Formalize and prove the fact that every node's `fresh`
       counter in its local state is strictly greater than any
       `uid` fields in messages it has sent in the network.
       Roughtly: if packet p sent by node n is in the network
       for world w, then n.fresh > p.payload.uid.
   *)  

  (* Mini Project

     Find and prove an inductive invariant that lets you
     establish the correctness of SeqNum.  If you get stuck,
     try following the analogous proofs under:
         ../verdi/systems/SeqNumCorrect.v

     Make sure to try figuring out the inductive invariant
     before you peek though!
   *)

End SeqNumProof.
