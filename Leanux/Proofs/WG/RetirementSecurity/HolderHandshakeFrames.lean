import Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshakeWorkers
import Leanux.Proofs.WG.Queues.HolderSendDispatch

/-! Native handshake construction and initiation transmission retain the exact
key-reference account. Their peer timer and cookie writes preserve only the
holder projection; key creation and final peer payment are handled separately. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderHandshake
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem index_points (action : IndexM α) : SameView ownershipPointView (liftIndex action) :=
  ownershipPoints_holderStore _ (index_holderStore action)

macro "holder_handshake_step " initial:term : tactic => `(tactic| first
  | (allocation_release_lift_from IndexM; exact (index_points _).wp (· = $initial))
  | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | (allocation_release_head unsupported; exact hoare_liftAmbient (AmbientM.unsupported _) _)
  | (allocation_release_head hidden; unfold hidden)
  | (allocation_release_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (allocation_release_head modify; apply hoare_modify; intro w before; exact before)
  | (allocation_release_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => ownershipPointView w = $initial))
  | (allocation_release_head hiddenClock64; unfold hiddenClock64)
  | (allocation_release_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ _)
  | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_head liftIndex; exact (index_points _).wp (· = $initial))
  | (allocation_release_head getDev
     exact (getDev_sameWGStore.of_factor (fun store => ownershipPointView {dev := store.dev})
       ownershipPointView (fun _ => rfl)).wp (· = $initial))
  | (allocation_release_head updatePeer; unfold updatePeer)
  | (allocation_release_head generatePublic; exact (generatePublic_sameWGWorld _).wp (fun w => ownershipPointView w = $initial))
  | (allocation_release_head messageEphemeral; exact (messageEphemeral_sameWGWorld _ _ _ _).wp (fun w => ownershipPointView w = $initial))
  | (allocation_release_head mixDh; exact (mixDh_sameWGWorld _ _ _ _).wp (fun w => ownershipPointView w = $initial))
  | (allocation_release_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp (fun w => ownershipPointView w = $initial))
  | (allocation_release_head messageDecrypt; exact (messageDecrypt_sameWGWorld _ _ _).wp (fun w => ownershipPointView w = $initial))
  | (allocation_release_head kdf; exact (Framing.kdf_sameWGWorld _ _ _ _).wp (fun w => ownershipPointView w = $initial))
  | (allocation_release_head kdfOut; exact (Framing.kdfOut_sameWGWorld _ _).wp (fun w => ownershipPointView w = $initial))
  | ownership_source_step $initial)

theorem create_initiation_points (pid : PeerId) : SameView ownershipPointView (createInitiation pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | holder_handshake_step initial

theorem create_response_points (pid : PeerId) : SameView ownershipPointView (createResponse pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | holder_handshake_step initial

theorem add_mac_points (pid : PeerId) (msg : List UInt8) : SameView ownershipPointView (addMacToPacket pid msg) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold addMacToPacket WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | holder_handshake_step initial

theorem socket4_points (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView ownershipPointView (send4 e cache bytes ds exactRx) :=
  (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OwnershipSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send4_ownership) e cache bytes ds exactRx

theorem socket6_points (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView ownershipPointView (send6 e cache bytes ds exactRx) :=
  (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OwnershipSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send6_ownership) e cache bytes ds exactRx

macro "holder_handshake_send " initial:term : tactic => `(tactic| first
  | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (fun w => ownershipPointView w = $initial))
  | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (fun w => ownershipPointView w = $initial))
  | (rx_retention_head armTimer; exact (armTimer_ownership _ _ _ _).wp (· = $initial))
  | (rx_retention_head modPeerTimerGuard; exact (modPeerTimerGuard_ownership _).wp (· = $initial))
  | (rx_retention_head delTimer; exact (delTimer_ownership _ _).wp (· = $initial))
  | (rx_retention_head modPeerTimer; exact (modPeerTimer_ownership _ _ _ _).wp (· = $initial))
  | (rx_retention_head send4; exact (socket4_points _ _ _ _ _).wp (· = $initial))
  | (rx_retention_head send6; exact (socket6_points _ _ _ _ _).wp (· = $initial))
  | holder_handshake_step $initial)

theorem buffer_points (pid : PeerId) (bytes : List UInt8) :
    SameView ownershipPointView (sendBufferToPeer pid bytes) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' holder_handshake_send initial

theorem initiated_points (pid : PeerId) : SameView ownershipPointView (timersHandshakeInitiated pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold timersHandshakeInitiated
  repeat' holder_handshake_send initial

theorem derived_points (pid : PeerId) : SameView ownershipPointView (timersSessionDerived pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold timersSessionDerived
  simp (config := {zeta := false}) only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' holder_handshake_send initial

theorem initiation_points (pid : PeerId) : SameView ownershipPointView (sendHandshakeInitiation pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head timersAnyAuthenticatedPacketSent; unfold timersAnyAuthenticatedPacketSent)
    | (rx_retention_head timersTraversal; exact (timersTraversal_ownership _).wp (· = initial))
    | (rx_retention_head createInitiation; exact (create_initiation_points _).wp (· = initial))
    | (rx_retention_head addMacToPacket; exact (add_mac_points _ _).wp (· = initial))
    | (rx_retention_head timersHandshakeInitiated; exact (initiated_points _).wp (· = initial))
    | (rx_retention_head sendBufferToPeer; exact (buffer_points _ _).wp (· = initial))
    | holder_handshake_send initial

theorem initiation (pid : PeerId) (temporary : Credits.Ledger) :
    Preserves (HolderAccount temporary) (sendHandshakeInitiation pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact before.points ((ProjectedAction.iff_run_ambient _ _ _).mp (initiation_points pid) w a result v b run)

end Leanux.Proofs.WG.RetirementSecurity.HolderHandshake
