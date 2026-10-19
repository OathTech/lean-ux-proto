import Leanux.Proofs.WG.RetirementSecurity.HandshakeSendDispatch
import Leanux.Proofs.WG.RetirementSecurity.ReceiveEntryHolders

/-! Actual responder handshake production composes fresh allocation and slot
rotation with its unchanged timer/socket suffix. The allocation witness is
transported by the existing native observer at each source cut. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderResponse
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits ReceiveEntry HolderHandshake

abbrev Ready := ReceiveEntry.Ready

theorem join {observer : MixedM α} {native : WG.M α}
    (erases : ErasesStatePrefix observer native)
    (allocation : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe observer)
    (keys : Preserves (HolderAccount temporary) native) : Preserves (Ready temporary) native := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp keys w a result v b before.1 run,
    Allocated.native erases allocation before.2 a b run⟩

theorem points {observer : MixedM α} {native : WG.M α}
    (erases : ErasesStatePrefix observer native)
    (allocation : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe observer)
    (same : SameView ownershipPointView native) : Preserves (Ready temporary) native :=
  join erases allocation (by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    exact before.points ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run))

theorem session (pid : PeerId) : Preserves (Ready temporary) (beginSession pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨before.1.session before.2.choose_spec pid a b run,
    Allocated.native (beginSessionPrefix_erases pid) (beginSessionPrefix_allocation pid) before.2 a b run⟩

theorem create (pid : PeerId) : Preserves (Ready temporary) (createResponse pid) :=
  points (HandshakeCall.erases (.createResponse pid)) (HandshakeCall.allocation (.createResponse pid))
    (create_response_points pid)

theorem mac (pid : PeerId) (bytes : List UInt8) : Preserves (Ready temporary) (addMacToPacket pid bytes) :=
  points (HandshakeCall.erases (.addMac pid bytes)) (HandshakeCall.allocation (.addMac pid bytes))
    (add_mac_points pid bytes)

theorem buffer (pid : PeerId) (bytes : List UInt8) : Preserves (Ready temporary) (sendBufferToPeer pid bytes) :=
  points (HandshakeSendCall.erases (.buffer pid bytes)) (HandshakeSendCall.allocation (.buffer pid bytes))
    (buffer_points pid bytes)

theorem derived (pid : PeerId) : Preserves (Ready temporary) (timersSessionDerived pid) :=
  points (HandshakeSendCall.erases (.sessionDerived pid)) (HandshakeSendCall.allocation (.sessionDerived pid))
    (derived_points pid)

theorem traversal (pid : PeerId) : Preserves (Ready temporary) (timersTraversal pid) :=
  points (MaintenanceCall.erases (.traversal pid)) (MaintenanceCall.allocation (.traversal pid))
    (timersTraversal_ownership pid)

theorem sent (pid : PeerId) : Preserves (Ready temporary) (timersAnyAuthenticatedPacketSent pid) :=
  points (MaintenanceCall.erases (.deleteTimer pid .sendKeepalive))
    (MaintenanceCall.allocation (.deleteTimer pid .sendKeepalive)) (delTimer_ownership pid .sendKeepalive)

theorem peer_update (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀ p, (f p).internalId = p.internalId)
    (fields : ∀ p, peerOwnership (f p) = peerOwnership p) :
    Preserves (Ready temporary) (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply join (modifyPeerKeysPrefix_erases pid f)
    (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient allocationAmbient (fun _ => True) pid f stamp))
  change Preserves (HolderAccount temporary) (updatePeer pid f)
  exact ownership_preserves _ (updatePeer_ownership pid f fields) temporary

theorem peer_update_bind (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (stamp : ∀ p, (f p).internalId = p.internalId)
    (fields : ∀ p, peerOwnership (f p) = peerOwnership p)
    (next : ∀ x, Preserves (Ready temporary) (tail x)) :
    Preserves (Ready temporary) (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (peer_update pid f stamp fields) next

macro "holder_response_step" : tactic => `(tactic| first
  | (receive_update_head setPeer; apply peer_update <;> intro p <;> rfl)
  | (receive_update_head Bind.bind
     apply peer_update_bind
     · intro p; rfl
     · intro p; rfl
     intro x)
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getDev; exact ReceiveEntry.store getDev_sameWGStore)
  | (rx_retention_head createResponse; exact create _)
  | (rx_retention_head addMacToPacket; exact mac _ _)
  | (rx_retention_head beginSession; exact session _)
  | (rx_retention_head timersSessionDerived; exact derived _)
  | (rx_retention_head timersTraversal; exact traversal _)
  | (rx_retention_head timersAnyAuthenticatedPacketSent; exact sent _)
  | (rx_retention_head sendBufferToPeer; exact buffer _ _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | rxstack_preserves_join
  | rx_retention_step)

/-- Response production may create and rotate a keypair, but its exact
reference account survives every normal refusal or successful send path. -/
theorem response (pid : PeerId) : Preserves (Ready temporary) (sendHandshakeResponse pid) := by
  unfold sendHandshakeResponse
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' holder_response_step

end Leanux.Proofs.WG.RetirementSecurity.HolderResponse
