import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRing
import Leanux.Proofs.WG.Packets.PublicationIdentity

/-! Decrypt preparation replaces existing RX payloads without allocating or
erasing their slots. The full Entry projection therefore remains equal;
this frame does not apply to ingress allocation or receive-cell disposal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDecrypt
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations Queues.RxCredits
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

theorem replace_rx (device : w.dev = some d) (resident : d.rxSkbs[skb]? = some packet)
    (next : RxPacket) :
    StagedEntry.view {w with dev := some {d with rxSkbs := d.rxSkbs.insert skb next}} = StagedEntry.view w := by
  unfold StagedEntry.view
  apply Prod.ext
  · simp [Packets.epoch,device]
  apply Prod.ext
  · funext pid; simp [Staged.stagedAt,device]
  apply Prod.ext
  · funext id; simp [PacketMaterial.view,TxDisposition.txPackets,device]
  apply Prod.ext
  · simpa only [Packets.snapshot,device] using Packets.deviceStore_setRx d skb packet next resident
  apply Prod.ext
  · funext id; simp [TxDisposition.txPackets,device]
  · funext pid; simp [txQueueContents,handoffTxView,device]

theorem set_rx (skb : SkbId) (f : RxPacket → RxPacket) : SameView StagedEntry.view (setRxSkb skb f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  cases device : w.dev with
  | none => simp [setRxSkb,liftSkb_run,device] at run
  | some d =>
    cases resident : d.rxSkbs[skb]? with
    | none =>
      simp [setRxSkb,liftSkb_run,SkbStore.setRx,SkbStore.getRx,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some packet =>
      rw [Packets.setRxSkb_run w a d skb packet f device resident] at run
      cases run
      simpa only [Packets.update,device,Option.map_some] using replace_rx device resident (f packet)

theorem packet (pkt : RxPacket) : SameView StagedEntry.view (decryptPacket pkt) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold decryptPacket WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc,invariant]
  repeat' first
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => StagedEntry.view w = initial))
    | entry_key_step initial

theorem publication (skb : SkbId) (state : PacketState) : SameView StagedEntry.view (RxWorkers.publishSource skb state) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a pid v b run
  obtain ⟨d,pkt,k,p,device,resident,_,_,peer,effect⟩ := PublicationIdentity.publish_execution skb state w v a b pid run
  have after := congrArg WGStoreView.dev effect
  change v.dev = some _ at after
  let u : WGWorld := {w with dev := some {d with rxSkbs := d.rxSkbs.insert skb {pkt with state}}}
  let t : WGWorld := {u with dev := some {d with rxSkbs := d.rxSkbs.insert skb {pkt with state}, peers := d.peers.insert pid {p with refcount := p.refcount+1}}}
  have rx : StagedEntry.view u = StagedEntry.view w := replace_rx device resident _
  have borrow : StagedEntry.view t = StagedEntry.view u :=
    Queued.replace_peer (w := u) rfl peer (q := {p with refcount := p.refcount+1}) rfl rfl rfl
  have finish := Queued.replace_peer (w := t) (pid := pid) (p := {p with refcount := p.refcount+1}) rfl (by simp)
    (q := {p with refcount := p.refcount+1,napiScheduled := true}) rfl rfl rfl
  change StagedEntry.view {dev := v.dev} = _
  rw [after]
  exact finish.trans (borrow.trans rx)

theorem prepare : SameView StagedEntry.view RxWorkers.prepareSource := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold RxWorkers.prepareSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head decryptPacket; exact packet _ initial)
    | (rx_retention_head RxWorkers.publishSource; exact publication _ _ initial)
    | (rx_retention_head getRxSkb; exact CompletePollNative.get_rx _ initial)
    | (rx_retention_head setRxSkb; exact set_rx _ _ initial)
    | entry_key_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDecrypt
