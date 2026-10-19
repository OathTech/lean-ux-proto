import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerNativeFrames
import Leanux.Proofs.WG.Queues.HolderDeviceCreate

/-! Actual guarded device creation has no hidden reference slack. The absent
entry and the fresh native empty peer map discharge the new upper account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

namespace DeviceCreate

theorem link (account : ExactBoundary carriers loans w) (same : linkView v=linkView w) :
    ExactBoundary carriers loans v := by
  apply account.fields
  rw [← (pinned_const _private.Leanux.Proofs.WG.Queues.HolderDeviceCreate.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceCreate.link_fields) v,
    ← (pinned_const _private.Leanux.Proofs.WG.Queues.HolderDeviceCreate.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceCreate.link_fields) w,same]

theorem empty_upper (empty : ∀ d, w.dev=some d → d.peers={}) : Upper holders carriers loans w := by
  intro owner
  cases device : w.dev with
  | none => simp [balance,resident,device]
  | some d => simp [balance,resident,device,empty d device]

theorem create : Preserves (ExactBoundary carriers loans) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b account run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨absent,fresh⟩
  · exact link account same
  · have shape := (pinned_const _private.Leanux.Proofs.WG.Queues.HolderDeviceCreate.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceCreate.fresh_empty) fresh
    obtain ⟨holders,funded,stable⟩ := (hoare_iff_run_ambient _ _ _).mp HolderDeviceCreate.create
      w a result v b account.lower run
    exact ⟨holders,funded,empty_upper (fun d found => (shape d found).1),stable⟩

end DeviceCreate
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
