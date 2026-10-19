import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationBatch
import Leanux.Proofs.WG.TransmitSecurity.CompletionEmission
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationSendResult

/-! Actual packet-read and free witnesses join the same historical allocation
ordinal. Receipt validity alone is not an ownership theorem: the current
physical backing and allocation identity remain visible inputs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open HandshakeSecurity.StagedConservation

theorem read_cell (read : RunWitness DataPacket)
    (valid : read.Valid (liftWG (getTxSkb skb))) :
    read.after.wg = read.before.wg ∧ TxDisposition.txPackets read.before.wg skb = some read.value := by
  change (liftWG (getTxSkb skb)).run read.before = .ok (read.value,read.after) at valid
  rw [liftWG_run] at valid
  cases native : ((getTxSkb skb).run read.before.wg).run read.before.ambient with
  | error stop => simp [native,Except.map] at valid
  | ok out =>
    rcases out with ⟨⟨value,wg⟩,ambient⟩
    have facts := Packets.getTxSkb_current skb read.before.wg wg value
      read.before.ambient ambient native
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at valid
    obtain ⟨same,clock,device,atDevice,resident⟩ := facts
    have result : value = read.value := valid.1
    have after : read.after.wg = wg := congrArg World.wg valid.2.symm
    refine ⟨after.trans same,?_⟩
    simp only [TxDisposition.txPackets,atDevice,Option.bind_some,resident,result]

/-- The read's actual payload, peer, key word and nonce belong to this exact
allocation occurrence. Ciphertext/state are intentionally absent from material. -/
theorem read_material (read : RunWitness DataPacket)
    (valid : read.Valid (liftWG (getTxSkb skb)))
    (backed : Backed history position ordinal read.before.wg)
    (origin : Origin history position ordinal generation skb value) :
    PacketMaterial.material read.value = value ∧
      packetStamp read.before.wg skb = (generation,skb+1) := by
  have actual := backed.at_origin origin
  have cell := (read_cell read valid).2
  have material : PacketMaterial.material read.value = value := by
    simpa only [PacketMaterial.view,cell,Option.map_some,Option.some.injEq] using actual.2
  refine ⟨material,?_⟩
  change ((Packets.epoch read.before.wg).getD 0,skb+1) = _
  rw [actual.1]
  rfl

/-- The actual inner socket receipt retains the allocation ordinal's packet
material and the socket's own endpoint/bytes emission fact. -/
theorem socket_material (receipt : Completion.SocketReceipt) (valid : receipt.Valid)
    (backed : Backed history position ordinal receipt.packet.before.wg)
    (origin : Origin history position ordinal generation receipt.id value) :
    PacketMaterial.material receipt.packet.value = value ∧
      packetStamp receipt.packet.before.wg receipt.id = (generation,receipt.id+1) ∧
      SocketEmission receipt.endpoint receipt.packet.value.bytes receipt.packet.value.ds
        receipt.socket.before.wg.sent receipt.socket.after.wg.sent :=
  ⟨(read_material receipt.packet valid.1 backed origin).1,
    (read_material receipt.packet valid.1 backed origin).2,valid.emission⟩

/-- The outer Boolean result, including unsupported-family false, uses the
same actual packet read. Whether an earlier inner socket result is already
terminal is a source-order question, not a consequence of this validity fact. -/
theorem send_result_material (receipt : SendResult.Receipt) (valid : receipt.Valid)
    (backed : Backed history position ordinal receipt.packet.before.wg)
    (origin : Origin history position ordinal generation receipt.skb value) :
    PacketMaterial.material receipt.packet.value = value ∧
      packetStamp receipt.packet.before.wg receipt.skb = (generation,receipt.skb+1) :=
  read_material receipt.packet valid.1 backed origin

/-- A native DEAD/create-refusal free erases this same backed cell. The
receipt's reason must still be established by its actual branch-labelled source. -/
theorem disposal_material (receipt : Terminal.Receipt) (valid : receipt.Valid)
    (backed : Backed history position ordinal receipt.run.before.wg)
    (origin : Origin history position ordinal generation receipt.skb value) :
    receipt.stamp = (generation,receipt.skb+1) ∧
      PacketMaterial.view receipt.run.before.wg receipt.skb = some value ∧
      PacketMaterial.view receipt.run.after.wg receipt.skb = none := by
  have actual := backed.at_origin origin
  exact ⟨receipt_stamp receipt actual.1,actual.2,(free_views receipt valid).2.1⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
