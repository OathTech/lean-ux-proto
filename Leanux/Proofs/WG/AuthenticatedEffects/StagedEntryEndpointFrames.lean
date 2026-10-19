import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveFrames

/-! Endpoint and route-cache maintenance retain the full staged-entry view.
The cached peer reads remain paired with their own writes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.EndpointFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity
set_option maxHeartbeats 600000

theorem reset (pid : PeerId) : SameView StagedEntry.view (dstCacheReset pid) := by
  unfold dstCacheReset
  apply SameView.bind (fun initial => hoare_liftAmbient (get : AmbientM Ambient)
    (fun w => StagedEntry.view w = initial))
  intro ambient
  apply SameView.bind (fun initial => hoare_consequence
    (hoare_get (fun w => StagedEntry.view w = initial)) (fun _ h => h) (fun _ _ h => h.2))
  intro world
  split
  · exact SameView.pure _ _
  · apply SameView.bind (fun initial => hoare_liftAmbient (AmbientM.hiddenJiffies .dstCacheResetTs)
      (fun w => StagedEntry.view w = initial))
    intro clock
    exact Queued.update pid (fun p => {p with dstCache := {p.dstCache with resetTs := clock}})
      (fun _ => ⟨rfl,rfl,rfl⟩)

theorem reset_now (pid : PeerId) : SameView StagedEntry.view (dstCacheResetNow pid) := by
  unfold dstCacheResetNow
  apply SameView.bind (reset pid)
  intro ignored
  exact Queued.update pid (fun p => {p with dstCache := {p.dstCache with slot := none}})
    (fun _ => ⟨rfl,rfl,rfl⟩)

theorem clear (pid : PeerId) : SameView StagedEntry.view (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc
  simpa only [bind_assoc] using SameView.bind
    (Queued.update pid (fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0,srcIf := 0}})
      (fun _ => ⟨rfl,rfl,rfl⟩)) (fun _ => reset_now pid)

theorem equal (endpoint : Endpoint) (old : Option Endpoint) :
    SameView StagedEntry.view (endpointEq endpoint old) :=
  TimerFrames.store (endpointEq_sameStore endpoint old)

theorem set (pid : PeerId) (endpoint : Endpoint) :
    SameView StagedEntry.view (setPeerEndpoint pid endpoint) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold setPeerEndpoint requireNotPending
  simp only [branch]
  repeat' first
    | (rx_retention_head endpointEq; exact (equal _ _).wp (· = initial))
    | (rx_retention_head dstCacheReset; exact (reset _).wp (· = initial))
    | entry_timer_native_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.EndpointFrames
