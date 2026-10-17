import Leanux.Proofs.WG.Origins.CurrentConfiguration
import Leanux.Proofs.WG.Origins.OwnerPeerConfiguration
import Leanux.Proofs.WG.Lifetimes.ConfigurationDevice

/-! Joint current-identity and receiving-owner preservation for actual native
configuration. Creation uses the joint frontier contract, and normal negative
errno results retain all partial updates. No return state is asserted on Stop. -/
namespace Leanux.Proofs.WG.JointOwnerConfiguration
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Configuration CurrentLifecycle CurrentTraffic ConfiguredHandshake OwnerControls

def Inv (history : List SessionOrigin.Receipt) (w : WGWorld) : Prop :=
  CurrentLifecycle.Inv history w ∧ OwnerBounds.Carrier w

private theorem combine {α : Type} (a : WG.M α) (history : List SessionOrigin.Receipt)
    (current : Preserves (CurrentLifecycle.Inv history) a)
    (owner : Preserves OwnerBounds.Carrier a) : Preserves (Inv history) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hi hr
  exact ⟨(hoare_iff_run_ambient _ _ _).mp current w ambient result v finalAmbient hi.1 hr,
    (hoare_iff_run_ambient _ _ _).mp owner w ambient result v finalAmbient hi.2 hr⟩

private theorem store {α : Type} (a : WG.M α) (same : SameWGStore a)
    (history : List SessionOrigin.Receipt) : Preserves (Inv history) a :=
  combine a history ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentLifecycle.«0».Leanux.Proofs.WG.CurrentLifecycle.store_preserves) a same history) (OwnerControls.store a same)

private theorem peerGet_owner (pid : PeerId) : Preserves OwnerBounds.Carrier (peerGet pid) := by
  unfold peerGet
  simp (config := {zeta := false}) only [requireNotPending,refcountInc,branch,branchCmp,unsupported]
  repeat' owner_control_step

private theorem maybeGet_owner (peer : Option PeerId) :
    Preserves OwnerBounds.Carrier (peerGetMaybeZero peer) := by
  unfold peerGetMaybeZero
  simp (config := {zeta := false}) only [branch,invariant,requireNotPending,refcountIncNotZero,branchCmp,unsupported]
  repeat' owner_control_step

private theorem pubkey_owner (key : Key) : Preserves OwnerBounds.Carrier (pubkeyLookup key) := by
  unfold pubkeyLookup
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head peerGetMaybeZero; exact maybeGet_owner _)
    | owner_control_step

theorem pubkeyLookup_preserves (key : Key) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (pubkeyLookup key) :=
  combine _ history
    (current_preserves _ (ConfiguredReceive.pubkeyLookup_view key)
      (Origins.Retaining.of_view (Origins.Retaining.pubkeyLookup_material key)) history)
    (pubkey_owner key)

private theorem peerGet_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (peerGet pid) := by
  apply combine _ history ?_ (peerGet_owner pid)
  current_traffic_step history

private theorem pay_preserves (peer : Option PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (peerPut peer) := by
  apply combine _ history ?_ (OwnerConsume.peerPut_preserves peer)
  current_traffic_step history

macro "joint_configuration_step " history:term : tactic => `(tactic| first
  | (rx_retention_head getDev; exact store _ getDev_sameWGStore $history)
  | (rx_retention_head peerGet; exact peerGet_preserves _ $history)
  | (rx_retention_head peerPut; exact pay_preserves _ $history)
  | (rx_retention_head pubkeyLookup; exact pubkeyLookup_preserves _ $history)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (Inv $history))
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Inv $history)
     intro x b
     change Preserves (Inv $history) _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w ambient result v finalAmbient hi hr
     cases hr)
  | rx_retention_step)

theorem peerConfigUpdate_preserves (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (peerConfigUpdateSource a peer flags psk pid) :=
  combine _ history (CurrentConfiguration.peerConfigUpdate_preserves a peer flags psk pid history)
    (OwnerPeerConfiguration.peerConfigUpdate_preserves a peer flags psk pid)

theorem setPeerCmd_preserves (a : PeerAttrs) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (setPeerCmd a) := by
  rw [← setPeerCmd_source]
  unfold setPeerCmdSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerCreate; exact OwnerCreation.peerCreate_current _ _ history)
    | (rx_retention_head peerConfigUpdateSource; exact peerConfigUpdate_preserves _ _ _ _ _ history)
    | joint_configuration_step history

/-- The existing lifetime observer preserves the joint positional checks,
including its failed journal prefixes and arbitrary incoming history. -/
theorem setPeerCmd_checked (a : PeerAttrs) :
    OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver (setPeerCmdPrefix a))) := by
  apply OwnerConfiguration.native_mixed _ _ (ConfigurationCall.erases (.peer a))
    (ConfigurationCall.allocation (.peer a)) (Origins.Retaining.setPeerCmd_material a)
  intro allocation history
  exact hoare_consequence (setPeerCmd_preserves a history)
    (fun _ hi => hi.2) (fun _ _ hi => hi)

end Leanux.Proofs.WG.JointOwnerConfiguration
