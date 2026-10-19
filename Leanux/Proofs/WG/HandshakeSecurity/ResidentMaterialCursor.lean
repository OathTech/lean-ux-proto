import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialFrames
import Leanux.Proofs.WG.Lifetimes.AllocationReleaseFrames

/-! The numeric key-slot frontier used to exclude session derivation from
earlier packet references. It is distinct from the global allocation stamp. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Origins

def cursor (w : WGWorld) : Option Nat := w.dev.map (·.nextKeypairId)
def Lower (bound : Nat) (w : WGWorld) : Prop :=
  ∀ front, cursor w = some front → bound ≤ front

theorem cursor_metadata {action : WG.M α} (frame : SameView allocationMetadata action) :
    SameView cursor action :=
  frame.of_factor (fun fields => fields.device.map (·.nextKeypair)) cursor
    (fun _ => by simp only [cursor,allocationMetadata,Option.map_map,Function.comp_def]; rfl)

theorem lower_frame {action : WG.M α} (frame : SameView cursor action) :
    Preserves (Lower bound) action := frame.wp (fun cell => ∀ front, cell = some front → bound ≤ front)

theorem lower_metadata {action : WG.M α} (frame : SameView allocationMetadata action) :
    Preserves (Lower bound) action := lower_frame (cursor_metadata frame)

theorem lower_key_create (word : Option PeerId) : Preserves (Lower bound) (keypairCreate word) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result with
  | none =>
    have same := create_none word w v a b run
    exact same ▸ hi
  | some id =>
    obtain ⟨d,device,_,rfl⟩ := create_some word w v id a b run
    intro front found
    have same : front = d.nextKeypairId + 1 := by simpa [cursor,keyAllocationWorld,keyAllocationDevice] using found.symm
    rw [same]
    exact Nat.le_trans (hi d.nextKeypairId (by simp [cursor,device])) (Nat.le_succ _)

theorem lower_index (action : IndexM α) : Preserves (Lower bound) (liftIndex action) := by
  apply hoare_liftIndex
  intro w d table hi device
  simpa only [Lower,cursor,device,Option.map_some] using hi

theorem lower_peer_read (pid : PeerId) : Preserves (Lower bound) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  exact (Origins.getPeer_return pid w v p a b run).1 ▸ hi

theorem lower_key_read (kid : KeypairId) : Preserves (Lower bound) (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a k v b hi run
  exact (KeyTimes.getKeypair_return kid w v k a b run).1 ▸ hi

macro "material_cursor_step" : tactic => `(tactic| first
  | (allocation_release_head getPeer; exact lower_peer_read _)
  | (allocation_release_head getKeypair; exact lower_key_read _)
  | (allocation_release_head setPeer; exact lower_metadata (setPeer_metadata _ _))
  | (allocation_release_head setKeypair; exact lower_metadata (setKeypair_metadata _ _))
  | (allocation_release_head keypairPut; exact lower_metadata ((keypairPut_rest _ _).factor (fun r => r.2.2)))
  | (allocation_release_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ _)
  | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_head liftIndex; exact lower_index _)
  | (allocation_release_head unsupported; exact hoare_liftAmbient (AmbientM.unsupported _) _)
  | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM; exact lower_index _)
  | allocation_release_step)

theorem lower_rotation (pid : PeerId) (kid : KeypairId) :
    Preserves (Lower bound) (addNewKeypair pid kid) := by
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' material_cursor_step

theorem lower_derive (kid : KeypairId) (initiator : Bool) (chain : List UInt8) :
    Preserves (Lower bound) (deriveKeys kid initiator chain) := by
  unfold deriveKeys
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' first
    | (allocation_release_head kdf; exact lower_frame ((kdf_sameWGWorld _ _ _ _).factor cursor))
    | (allocation_release_head kdfOut; exact lower_frame ((kdfOut_sameWGWorld _ _).factor cursor))
    | material_cursor_step

theorem lower_zero (pid : PeerId) : Preserves (Lower bound) (handshakeZero pid) := by
  unfold handshakeZero
  repeat' material_cursor_step

theorem lower_session (pid : PeerId) : Preserves (Lower bound) (beginSession pid) := by
  unfold beginSession WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head keypairCreate; exact lower_key_create _)
    | (allocation_release_head addNewKeypair; exact lower_rotation _ _)
    | (allocation_release_head deriveKeys; exact lower_derive _ _ _)
    | (allocation_release_head handshakeZero; exact lower_zero _)
    | material_cursor_step

theorem session_cursor (pid : PeerId) (w v : WGWorld) (a b : Ambient) (result : Bool)
    (before : w.dev = some d) (after : v.dev = some e)
    (run : ((beginSession pid).run w).run a = .ok ((result,v),b)) :
    d.nextKeypairId ≤ e.nextKeypairId := by
  have entry : Lower d.nextKeypairId w := by
    intro front found
    have same : front = d.nextKeypairId := by simpa [cursor,before] using found.symm
    rw [same]
    exact Nat.le_refl _
  exact (hoare_iff_run_ambient _ _ _).mp (lower_session pid) w a result v b entry run
    e.nextKeypairId (by simp [cursor,after])

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
