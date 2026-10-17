import Leanux.WG.Timers
import Leanux.Proofs.Framing.Projection
import Leanux.Proofs.Framing.Lift
import Leanux.Proofs.WG.Peers.Primitives

/-! The zero-key timer's immediate action is a queue operation, not a
clearance of transport keys. This contract concerns the callback only. -/
namespace Leanux.Proofs.WG.KeyTimes
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

def keypairStore (w : WGWorld) : Option (Std.TreeMap KeypairId Keypair) :=
  w.dev.map (·.keypairs)

theorem expiredZeroKeyMaterial_store (pid : PeerId) :
    SameView keypairStore (expiredZeroKeyMaterial pid) := by
  intro before
  let P := fun w : WGWorld => keypairStore w = before
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have index (a : IndexM Unit) : Preserves P (monadLift a : WG.M Unit) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    simpa [P, keypairStore, hd] using hi
  have read (i : PeerId) : Preserves P (getPeer i) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v a' hi hr
    have he := (Peers.getPeer_current i w v p a a' hr).1
    simpa only [he] using hi
  have device : Preserves P getDev := by
    unfold getDev
    apply preserves_bind (hoare_consequence (hoare_get P)
      (fun _ h => h) (fun _ _ h => h.2))
    intro w
    cases w.dev
    · exact ambient (AmbientM.invariant _)
    · exact preserves_pure _
  have write (f : Device → Device) (hf : ∀ d, (f d).keypairs = d.keypairs) :
      Preserves P (modifyDev f) := by
    apply hoare_modify
    intro w hi
    simpa [P, keypairStore, Option.map_map, Function.comp_def, hf] using hi
  have acquire (count : Nat) : Preserves P (refcountInc count : WG.M Unit) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v a' hi hr
    by_cases zero : count = 0 <;> by_cases overflow : 2147483647 ≤ count <;>
      simp [refcountInc, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
        unsupported, AmbientM.unsupported, zero, overflow] at hr
    all_goals try (change Except.error _ = Except.ok _ at hr; cases hr)
    all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals exact hi
  have release (count : Nat) : Preserves P (refcountDecAndTest count : WG.M Bool) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v a' hi hr
    by_cases pos : 0 < count <;> by_cases one : count = 1 <;>
      by_cases zero : count = 0 <;> by_cases under : count < 1 <;>
      simp [refcountDecAndTest, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
        unsupported, AmbientM.unsupported, pos, one, zero, under] at hr
    all_goals try (change Except.error _ = Except.ok _ at hr; cases hr)
    all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals exact hi
  have branchRule {α : Type} (decision : Decision) (value : Bool)
      (f : Bool → WG.M α) (hf : Preserves P (f value)) :
      Preserves P ((branch decision value : WG.M Bool) >>= f) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v a' hi hr
    change ((f value).run w).run _ = .ok ((x, v), a') at hr
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ hi hr
  have takePeer (i : PeerId) : Preserves P (peerGet i) := by
    unfold peerGet requireNotPending
    simp only [pure_bind]
    apply preserves_bind (read i)
    intro p
    apply preserves_bind (acquire p.refcount)
    intro _
    exact write _ (fun _ => rfl)
  have putPeer (i : PeerId) : Preserves P (peerPut (some i)) := by
    unfold peerPut
    apply branchRule .peerPutNull false
    simp only [Bool.false_eq_true, ↓reduceIte, requireNotPending, pure_bind]
    apply preserves_bind (read i)
    intro p
    apply preserves_bind (write (fun d => {d with peers := d.peers.insert i {p with refcount := p.refcount - 1}}) (fun _ => rfl))
    intro _
    apply preserves_bind (release p.refcount)
    intro released
    apply branchRule .peerKrefPutReleased released
    cases released <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact preserves_pure ()
    · apply preserves_bind (index (indexRemove (.handshake i)))
      intro _
      split
      · apply (hoare_iff_run_ambient _ _ _).mpr
        intro w a x v a' _ hr
        cases hr
      · apply preserves_bind (write
          (fun d => {d with txDropped := d.txDropped + p.staged.length, peers := d.peers.erase i})
          (fun _ => rfl))
        intro _
        split
        · apply (hoare_iff_run_ambient _ _ _).mpr
          intro w a x v a' _ hr
          cases hr
        · unfold retirePeerUnits modifyAmbient
          apply preserves_bind (ambient (modify _ : AmbientM Unit))
          intro _
          apply hoare_modify
          intro w hi
          exact hi
  unfold expiredZeroKeyMaterial
  apply preserves_bind (read pid)
  intro p
  apply branchRule .zeroKeyAlive (!p.isDead)
  cases p.isDead <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  · apply preserves_bind (takePeer pid)
    intro _
    apply preserves_bind device
    intro d
    apply preserves_bind (ambient (AmbientM.peekQueuedUnit .clearPeerWorker pid))
    intro queued
    apply branchRule .zeroKeyAlreadyQueued (d.clearWorkQueue.contains pid && !queued)
    split
    · exact putPeer pid
    · apply preserves_bind (ambient (AmbientM.recordQueued .clearPeerWorker pid))
      intro _
      exact write _ (fun _ => rfl)
  · exact preserves_pure ()

end Leanux.Proofs.WG.KeyTimes
