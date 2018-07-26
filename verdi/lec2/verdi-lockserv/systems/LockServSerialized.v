Require Import Verdi.Verdi.

Require Import Cheerios.Cheerios.
Require Import Verdi.SerializedMsgParams.
Require Import Verdi.SerializedMsgParamsCorrect.

Require Import LockServ.

Import DeserializerNotations.

Definition Msg_serialize (m : Msg) : IOStreamWriter.t :=
match m with
| Lock i => serialize x00 +$+ serialize i
| Unlock => serialize x01
| Locked i => serialize x02 +$+ serialize i
end.

Definition Msg_deserialize : ByteListReader.t Msg :=
tag <- deserialize ;;
match tag with
| x00 => Lock <$> deserialize
| x01 => ByteListReader.ret Unlock
| x02 => Locked <$> deserialize
| _ => ByteListReader.error
end.

Lemma Msg_serialize_deserialize_id :
  serialize_deserialize_id_spec Msg_serialize Msg_deserialize.
Proof.
  intros.
  unfold Msg_serialize, Msg_deserialize.
  destruct a;
   repeat (cheerios_crush; simpl);
   rewrite nat_serialize_deserialize_id; reflexivity.
Qed.

Instance Msg_Serializer : Serializer Msg :=
  {| serialize := Msg_serialize;
     deserialize := Msg_deserialize;
     serialize_deserialize_id := Msg_serialize_deserialize_id
  |}.

Section Serialized.
  Variable num_Clients : nat.

  Definition orig_base_params := LockServ_BaseParams num_Clients.
  Definition orig_multi_params := LockServ_MultiParams num_Clients.

  Instance transformed_base_params : BaseParams :=
    @serialized_base_params orig_base_params.

  Instance transformed_multi_params : MultiParams _ :=
    @serialized_multi_params orig_base_params orig_multi_params Msg_Serializer.
  
  Theorem transformed_correctness :
    forall net tr,
      step_async_star step_async_init net tr ->
      @mutual_exclusion num_Clients (nwState (deserialize_net net)).
  Proof using.
    intros.
    apply step_async_deserialized_simulation_star in H.
    break_exists.
    break_and.
    apply (@true_in_reachable_mutual_exclusion num_Clients).
    exists x; apply H.
  Qed.
End Serialized.
