import Leanux.Proofs.WG.HandshakeSecurity.FreshnessHandshakeFrames
import Leanux.Proofs.WG.Peers.CreationAccess

/-! The native peer-allocation exception to timestamp retention. Creation uses
its actual process-global allocation counter; an old numeric slot is not an
allocation identity. The generic source contract below keeps its allocation
obligation explicit for the initialized history carrier. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Freshness
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

/-- A creation either retains a prior allocation/timestamp, or introduces the
actual next allocation with the source's initial zero timestamp. -/
def CreationRetains (before after : WGWorld) : Prop :=
  ∀ pid stamp, freshnessAt after pid = some stamp →
    freshnessAt before pid = some stamp ∨
      stamp = (before.peerCounter + 1, List.replicate 12 0)

theorem creation_core (pid : PeerId) (key : Key) (w : WGWorld) :
    CreationRetains w (Peers.creationCoreWorld w pid key) := by
  intro q stamp found
  cases hd : w.dev with
  | none => simp [freshnessAt,Peers.creationCoreWorld,hd] at found
  | some d =>
    by_cases same : pid = q
    · subst q
      right
      simpa [freshnessAt,Peers.creationCoreWorld,Peers.createdPeer,hd] using found.symm
    · left
      simpa [freshnessAt,Peers.creationCoreWorld,hd,Std.TreeMap.getElem?_insert,same] using found

theorem creation_core_run (pid : PeerId) (key : Key)
    (w v : WGWorld) (a b : Ambient) (x : Unit)
    (run : (((Peers.peerCreateCore pid key).run w).run a) = .ok ((x,v),b)) :
    CreationRetains w v ∧ v.peerCounter = w.peerCounter + 1 := by
  rw [Peers.peerCreateCore_run] at run
  cases run
  exact ⟨creation_core pid key w,rfl⟩

theorem frame_preserves (action : WG.M α) (frame : Frame action)
    (P : WGWorld → Prop)
    (retained : ∀ w v, P w → RetainsFreshness w v → P v) :
    Framing.Preserves P action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  apply retained w v hi
  exact (hoare_iff_run_ambient _ _ _).mp (frame w) w a result v b (.refl w) run

theorem reset_sent (pid : PeerId) : Frame (resetLastSentHandshake pid) := by
  intro initial
  unfold resetLastSentHandshake
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' freshness_handshake_step initial

theorem precompute (pid : PeerId) : Frame (precomputeStaticStatic pid) := by
  apply of_view
  intro initial
  let P := fun w : WGWorld => freshnessAt w = initial
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Framing.Preserves Q (StateT.lift a) := hoare_liftAmbient a Q
  have clear : Framing.Preserves P (do
      let current ← getPeer pid
      setPeer pid {current with precomputedStaticStatic := List.replicate 32 0}) := by
    apply hoare_bind _ _ (read_saved (fun t => t = initial) pid)
    intro p
    exact write_saved (fun t => t = initial) pid _
  simp only [precomputeStaticStatic,requireNotPending,pure_bind]
  apply hoare_bind _ _ ((getDev_sameWGStore.factor
    (fun s : WGStoreView => fun p => (s.dev.bind fun d => d.peers[p]?).map
      fun peer => (peer.internalId,peer.latestTimestamp))).wp (fun t => t = initial))
  intro d
  apply hoare_bind _ _ (read_saved (fun t => t = initial) pid)
  intro p
  apply hoare_bind _ _ (ambient (AmbientM.branch .precomputeNoIdentity !d.staticIdentity.hasIdentity)
    (fun w => P w ∧ freshnessAt w pid = some (p.internalId,p.latestTimestamp)))
  intro noIdentity
  cases noIdentity with
  | true => exact hoare_consequence clear (fun _ h => h.1) (fun _ _ h => h)
  | false =>
    apply hoare_bind _ _ (write_saved (fun t => t = initial) pid _)
    intro _
    apply preserves_bind (ambient (AmbientM.branch .precomputeNullPoint
      !(curve25519 d.staticIdentity.staticPrivate p.remoteStatic).2) P)
    intro zero
    cases zero
    · exact preserves_pure _
    · exact clear

theorem handshake_init (pid : PeerId) (psk : Option Key) : Frame (handshakeInit pid psk) := by
  intro initial
  unfold handshakeInit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head IndexOwner.setPeerWord; exact owner_write _ _ initial)
    | (rx_retention_head precomputeStaticStatic; exact precompute _ initial)
    | freshness_handshake_step initial

theorem cache_reset (pid : PeerId) : Frame (dstCacheReset pid) := by
  intro initial
  unfold dstCacheReset
  simp (config := {zeta := false}) only [hiddenJiffies]
  repeat' first
    | (rx_retention_head getAmbient; exact hoare_liftAmbient (get : AmbientM Ambient) _)
    | freshness_handshake_step initial

/-- Whole native creation transports any carrier closed under retained-peer
frames, provided the actual allocation core preserves that carrier. This is
an explicit core obligation, not an initialized-history claim. -/
theorem peer_create (key : Key) (psk : Option Key) (P : WGWorld → Prop)
    (retained : ∀ w v, P w → RetainsFreshness w v → P v)
    (created : ∀ pid, Framing.Preserves P (Peers.peerCreateCore pid key)) :
    Framing.Preserves P (peerCreate key psk) := by
  rw [← Peers.peerCreateFactored_eq]
  unfold Peers.peerCreateFactored
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc]
  repeat' first
    | (rx_retention_head Peers.peerCreateCore; exact created _)
    | (rx_retention_head dstCacheReset; exact frame_preserves _ (cache_reset _) P retained)
    | (rx_retention_head handshakeInit; exact frame_preserves _ (handshake_init _ _) P retained)
    | (rx_retention_head resetLastSentHandshake; exact frame_preserves _ (reset_sent _) P retained)
    | (rx_retention_head getDev; exact frame_preserves _ (store _ getDev_sameWGStore) P retained)
    | (rx_retention_head modifyDev
       apply frame_preserves _ _ P retained
       apply modify_device
       intro d
       rfl)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ P)
    | rx_retention_step

end Leanux.Proofs.WG.HandshakeSecurity.Freshness
