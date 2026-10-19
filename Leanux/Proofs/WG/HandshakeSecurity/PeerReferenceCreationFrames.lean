import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceHandshakeFrames

/-! Actual peer allocation, identity setup and cache reset maintain reference
positivity. Allocation is proved from the original constructor. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

theorem reset_sent (pid : PeerId) :
    Framing.Preserves Inv (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' peer_reference_handshake_step

theorem precompute (pid : PeerId) :
    Framing.Preserves Inv (precomputeStaticStatic pid) := by
  let P := Inv
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Framing.Preserves Q (StateT.lift a) := hoare_liftAmbient a Q
  have clear : Framing.Preserves P (do
      let current ← getPeer pid
      setPeer pid {current with precomputedStaticStatic := List.replicate 32 0}) :=
    update_peer pid (fun p => {p with precomputedStaticStatic := List.replicate 32 0}) (fun _ positive => positive)
  simp only [precomputeStaticStatic,requireNotPending,pure_bind]
  apply hoare_bind _ _ (store getDev_sameWGStore)
  intro d
  apply hoare_bind _ _ (read_saved pid)
  intro p
  apply hoare_bind _ _ (ambient (AmbientM.branch .precomputeNoIdentity !d.staticIdentity.hasIdentity)
    (fun w => P w ∧ 0 < p.refcount))
  intro noIdentity
  cases noIdentity with
  | true => exact hoare_consequence clear (fun _ h => h.1) (fun _ _ h => h)
  | false =>
    apply hoare_bind _ _ (write_saved pid p (fun current => {current with precomputedStaticStatic :=
      (curve25519 d.staticIdentity.staticPrivate p.remoteStatic).1}) (fun _ => rfl))
    intro _
    apply preserves_bind (ambient (AmbientM.branch .precomputeNullPoint
      !(curve25519 d.staticIdentity.staticPrivate p.remoteStatic).2) P)
    intro zero
    cases zero
    · exact preserves_pure _
    · exact clear

theorem handshake_init (pid : PeerId) (psk : Option Key) :
    Framing.Preserves Inv (handshakeInit pid psk) := by
  unfold handshakeInit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head IndexOwner.setPeerWord; exact owner_write _ _)
    | (rx_retention_head precomputeStaticStatic; exact precompute _)
    | peer_reference_handshake_step

theorem cache_reset (pid : PeerId) :
    Framing.Preserves Inv (dstCacheReset pid) := by
  unfold dstCacheReset
  simp (config := {zeta := false}) only [hiddenJiffies]
  repeat' first
    | (rx_retention_head getAmbient; exact hoare_liftAmbient (get : AmbientM Ambient) _)
    | peer_reference_handshake_step

theorem creation_core (pid : PeerId) (key : Key) :
    Framing.Preserves Inv (Peers.peerCreateCore pid key) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  rw [Peers.peerCreateCore_run] at run
  cases run
  have kept := replace hi pid (Peers.createdPeer key (w.peerCounter + 1)) (by change 0 < 1; decide)
  simpa [Inv,Positive,view,Peers.creationCoreWorld,Option.bind_map,Function.comp_def] using kept

/-- The native peer constructor creates a positive resident and preserves
positivity of all other peers, including when a supplied slot is occupied. -/
theorem peer_create (key : Key) (psk : Option Key) :
    Framing.Preserves Inv (peerCreate key psk) := by
  rw [← Peers.peerCreateFactored_eq]
  unfold Peers.peerCreateFactored
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc]
  repeat' first
    | (rx_retention_head Peers.peerCreateCore; exact creation_core _ _)
    | (rx_retention_head dstCacheReset; exact cache_reset _)
    | (rx_retention_head handshakeInit; exact handshake_init _ _)
    | (rx_retention_head resetLastSentHandshake; exact reset_sent _)
    | peer_reference_handshake_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
