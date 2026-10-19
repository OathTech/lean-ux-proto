import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveFrames
import Leanux.Proofs.WG.Queues.RxBorrow

/-! The actual source lookup changes only its acquired peer reference.
Its exact native borrowed-state specification supplies the full Entry view. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ReceiveLookup
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity

theorem frame (protocol : Nat) (bytes : List UInt8) :
    SameView StagedEntry.view (lookupSrc protocol bytes) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupSrc_spec protocol bytes (wgStoreView w)) w a result v b rfl run
  cases result with
  | none =>
    change wgStoreView v = wgStoreView w at borrowed
    have same : v.dev = w.dev := congrArg WGStoreView.dev borrowed
    change StagedEntry.view {dev := v.dev} = StagedEntry.view {dev := w.dev}
    rw [same]
  | some pid =>
    obtain ⟨d,p,device,resident,_,after⟩ := borrowed
    change w.dev = some d at device
    have same := congrArg WGStoreView.dev after
    change v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount+1}} at same
    change StagedEntry.view {dev := v.dev} = _
    rw [same]
    exact Queued.replace_peer device resident (q := {p with refcount := p.refcount+1}) rfl rfl rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ReceiveLookup
