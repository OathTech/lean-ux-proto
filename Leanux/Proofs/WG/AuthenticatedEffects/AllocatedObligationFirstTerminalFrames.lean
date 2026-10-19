import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationInjectiveFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationReceipts
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginFrames
import Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames

/-! Socket handoff changes neither the allocation epoch nor any resident TX
cell. These native frames also hold for a socket errno. They justify retaining
physical cleanup debt after a first terminal result, independently of queues. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity

theorem socket_wire (receipt : Completion.SocketReceipt) :
    SameView RetirementSecurity.txCryptWire receipt.action := by
  unfold Completion.SocketReceipt.action
  cases receipt.ipv4
  · exact (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send6_cryptWire) _ _ _ _ _
  · exact (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send4_cryptWire) _ _ _ _ _

/-- The actual inner socket result, successful or errno, leaves every packet
cell resident with the same bytes, material and allocation epoch. -/
theorem socket_views (receipt : Completion.SocketReceipt) (native : receipt.Valid) :
    Packets.epoch receipt.socket.after.wg = Packets.epoch receipt.socket.before.wg ∧
      TxDisposition.txPackets receipt.socket.after.wg = TxDisposition.txPackets receipt.socket.before.wg ∧
      PacketMaterial.view receipt.socket.after.wg = PacketMaterial.view receipt.socket.before.wg := by
  have frame := sameView_liftWG (fun w : World => RetirementSecurity.txCryptWire w.wg)
    RetirementSecurity.txCryptWire receipt.action (socket_wire receipt) (fun _ _ _ same => same)
  have same := (ProjectedAction.iff_run _ _ _).mp frame _ _ _ native.2.2
  have cells := congrArg Prod.snd same
  have epoch := congrArg (fun wire => wire.1.map Prod.fst) same
  refine ⟨?_,cells,?_⟩
  · simpa only [RetirementSecurity.txCryptWire,TxRing.nativeCell,Packets.epoch,
      Option.map_map,Function.comp_def] using epoch
  · exact congrArg (fun cells id => (cells id).map PacketMaterial.material) cells

theorem socket_resident (receipt : Completion.SocketReceipt) (native : receipt.Valid)
    (resident : Resident history ledger receipt.socket.before.wg) :
    Resident history ledger receipt.socket.after.wg := by
  have views := socket_views receipt native
  exact fun ticket position ordinal member =>
    (resident ticket position ordinal member).views views.1 views.2.2

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
