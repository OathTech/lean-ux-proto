import Leanux.Proofs.WG.Origins.OwnerRemoval

/-! Native device lifecycle operations retain receiving-owner bounds, including
source refusals and queued-work Stops. Destruction may erase the device. -/
namespace Leanux.Proofs.WG.OwnerDevice
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Queues.RxCredits OwnerBounds OwnerControls OwnerLifecycle

private theorem rootRemovePeerLists_preserves (root : NodeId) :
    Preserves Carrier (rootRemovePeerLists root) := by
  unfold rootRemovePeerLists
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch,invariant]
  repeat' first
    | (allocation_release_head listDel; exact OwnerAllowedIps.listDel_preserves _)
    | owner_allowedip_step

theorem allowedipsFree_preserves : Preserves Carrier WG.free := by
  unfold WG.free
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head rootRemovePeerLists; exact rootRemovePeerLists_preserves _)
    | owner_allowedip_step

theorem peerRemoveAll_preserves : Preserves Carrier peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head WG.free; exact allowedipsFree_preserves)
    | (allocation_release_head peerMakeDead; exact OwnerRemoval.peerMakeDead_preserves _)
    | (allocation_release_head peerRemoveAfterDead; exact OwnerRemoval.peerRemoveAfterDead_preserves _)
    | owner_lifecycle_step

private theorem purgeStaged_preserves (pid : PeerId) : Preserves Carrier (purgeStagedPackets pid) := by
  unfold purgeStagedPackets
  repeat' owner_control_step

private theorem resetHandshake_preserves (pid : PeerId) : Preserves Carrier (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' owner_control_step

private theorem socketReinit_preserves (new4 new6 : Option Nat) :
    Preserves Carrier (socketReinit new4 new6) := by
  unfold socketReinit
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head sockFree; exact (sockFree_sameWGWorld _).wp Carrier)
    | owner_control_step

theorem wgStop_preserves : Preserves Carrier wgStop := by
  unfold wgStop
  simp (config := {zeta := false}) only [branch,unsupported,requireNotPending]
  repeat' first
    | (allocation_release_head purgeStagedPackets; exact purgeStaged_preserves _)
    | (allocation_release_head timersStop; exact timersStop_preserves _)
    | (allocation_release_head handshakeClear; exact handshakeClear_preserves _)
    | (allocation_release_head keypairsClear; exact keypairsClear_preserves _)
    | (allocation_release_head resetLastSentHandshake; exact resetHandshake_preserves _)
    | (allocation_release_head socketReinit; exact socketReinit_preserves _ _)
    | owner_lifecycle_step

theorem wgDown_preserves : Preserves Carrier wgDown := by
  unfold wgDown
  repeat' first
    | (allocation_release_head wgStop; exact wgStop_preserves)
    | owner_lifecycle_step

theorem absent (w : WGWorld) (hd : w.dev = none) : Carrier w := by
  constructor
  · intro d h
    simp [hd] at h
  · intro d id pkt h
    simp [hd] at h
  · intro d h
    simp [hd] at h

private theorem ratelimiterUninit_preserves : Preserves Carrier ratelimiterUninit := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi hr
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    ratelimiterUninit_sameRatelimiter w a x v b hr
  exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_sameDev)
    hi (congrArg WGStoreView.dev same)

theorem wgDestruct_preserves : Preserves Carrier wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (allocation_release_head socketReinit; exact socketReinit_preserves _ _)
    | (allocation_release_head peerRemoveAll; exact peerRemoveAll_preserves)
    | (allocation_release_head mayHaveSlept; exact store _ mayHaveSlept_sameWGStore)
    | (allocation_release_head ratelimiterUninit; exact ratelimiterUninit_preserves)
    | (allocation_release_head modify; apply hoare_modify; intro w hi; exact absent _ rfl)
    | (allocation_release_head retireDeviceUnits; exact store _ retireDeviceUnits_sameWGStore)
    | owner_lifecycle_step

end Leanux.Proofs.WG.OwnerDevice
