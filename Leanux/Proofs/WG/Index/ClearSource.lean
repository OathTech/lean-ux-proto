import Leanux.Proofs.WG.Index.ClearFrames
import Leanux.Proofs.WG.Index.StagedSource
import Leanux.Env

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The original immediate handshake unhash, followed by the peer-store reset. -/
theorem handshakeClear_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ handshakeClear pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have read : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient p final after pre run).1
  have deref : Ensures (IndexOwner.peerDeref (.handshake pid))
      TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold IndexOwner.peerDeref IndexOwner.peerWord
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ ?_
    · refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ read ?_
      intro p g ambient result final after pre run
      cases run
      exact pre
    · intro word
      cases word with
      | none =>
        exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
          (AmbientM.unsupported "entry->peer is NULL: the C dereferences it") TablesSafeWG)
      | some target =>
        intro g ambient result final after pre run
        cases run
        exact pre
  apply (ensures_iff _ _ _).mp
  unfold handshakeClear
  refine ensures_bind _ _ deref ?_
  intro _
  exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (indexRemove_tables (.handshake pid)))
    (fun _ => (ensures_iff _ _ _).mpr (handshakeZero_tables pid))

/-- Each actual immediate put filters the table. No slot distinctness or static
release budget is needed for preservation on normal return. -/
theorem keypairsClear_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ keypairsClear pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have read : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient p final after pre run).1
  apply (ensures_iff _ _ _).mp
  unfold keypairsClear
  refine ensures_bind _ _ read ?_
  intro p
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (modifyPeer_tables pid _)) ?_
  intro _
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (keypairPut_tables p.keypairNext true)) ?_
  intro _
  refine ensures_bind _ _ read ?_
  intro p
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (modifyPeer_tables pid _)) ?_
  intro _
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (keypairPut_tables p.keypairPrevious true)) ?_
  intro _
  refine ensures_bind _ _ read ?_
  intro p
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (modifyPeer_tables pid _)) ?_
  intro _
  exact (ensures_iff _ _ _).mpr (keypairPut_tables p.keypairCurrent true)

theorem queuedExpiredZeroKeyMaterial_tables (pid : PeerId) :
    Ensures (queuedExpiredZeroKeyMaterial pid) TablesSafeWG (fun _ => TablesSafeWG) := by
  unfold queuedExpiredZeroKeyMaterial
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (handshakeClear_tables pid)) ?_
  intro _
  exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (keypairsClear_tables pid))
    (fun _ => (ensures_iff _ _ _).mpr (peerPut_tables (some pid)))

/-- Original named/head selection, actual queue removal and section-wrapped body.
Malformed selection or release states retain the original stopped outcomes. -/
theorem runOneClearWorker_tables : Noise.Product.Ensures Env.runOneClearWorker
    (fun w => TablesSafeWG w.wg) (fun _ w => TablesSafeWG w.wg) := by
  let P : World → Prop := fun w => TablesSafeWG w.wg
  change Noise.Product.Ensures _ P (fun _ => P)
  have lifted {α : Type} (action : WG.M α)
      (contract : Ensures action TablesSafeWG (fun _ => TablesSafeWG)) :
      Noise.Product.Ensures (liftWG action) P (fun _ => P) := by
    intro w result final pre run
    change (((action.run w.wg).run w.ambient) >>= fun ((value, current), inputs) =>
      .ok (value, {w with wg := current, ambient := inputs})) = _ at run
    cases executed : (action.run w.wg).run w.ambient with
    | error stop => rw [executed] at run; cases run
    | ok pair =>
      obtain ⟨⟨value, current⟩, inputs⟩ := pair
      rw [executed] at run
      cases run
      exact contract w.wg w.ambient _ current inputs pre executed
  have ambient {α : Type} (action : AmbientM α) :
      Noise.Product.Ensures (liftAmbient action) P (fun _ => P) := by
    intro w result final pre run
    change (action.run w.ambient >>= fun (value, inputs) =>
      .ok (value, {w with ambient := inputs})) = _ at run
    cases executed : action.run w.ambient with
    | error stop => rw [executed] at run; cases run
    | ok pair =>
      obtain ⟨value, inputs⟩ := pair
      rw [executed] at run
      cases run
      exact pre
  have dev : Noise.Product.Ensures (liftWG getDev) P (fun _ => P) := by
    apply lifted
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have pureValue {α : Type} (value : α) :
      Noise.Product.Ensures (pure value : Leanux.M α) P (fun _ => P) := by
    intro w result final pre run
    cases run
    exact pre
  have worker (pid : PeerId) : Noise.Product.Ensures
      (Env.runWorker .clearPeerWorker (liftWG (queuedExpiredZeroKeyMaterial pid)))
      P (fun _ => P) := by
    unfold Env.runWorker
    refine Noise.Product.ensures_bind _ _ (ambient (AmbientM.hidden (.sectionStart .clearPeerWorker))) ?_
    intro _
    refine Noise.Product.ensures_bind _ _ (lifted _ (queuedExpiredZeroKeyMaterial_tables pid)) ?_
    intro _
    refine Noise.Product.ensures_bind _ _ (ambient (AmbientM.hidden (.sectionStop .clearPeerWorker))) ?_
    intro _
    exact pureValue ()
  unfold Env.runOneClearWorker
  refine Noise.Product.ensures_bind _ _ dev ?_
  intro d
  cases head : d.clearWorkQueue.head? with
  | none =>
    exact ambient (AmbientM.invariant "no queued clear work")
  | some headPid =>
    refine Noise.Product.ensures_bind _ _ (ambient (AmbientM.peekUnit .clearPeerWorker)) ?_
    intro named
    have tail (pid : PeerId) : Noise.Product.Ensures (do
        liftWG (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})
        Env.runWorker .clearPeerWorker (liftWG (queuedExpiredZeroKeyMaterial pid)))
        P (fun _ => P) := by
      refine Noise.Product.ensures_bind _ _ (lifted _ ((ensures_iff _ _ _).mpr
        (modifyClearWorkQueue_tables (fun queue => queue.erase pid)))) ?_
      intro _
      exact worker pid
    cases named with
    | none => exact Noise.Product.ensures_bind _ _ (pureValue headPid) tail
    | some unit =>
      exact Noise.Product.ensures_bind _ _
        (ambient (AmbientM.resolveUnit .clearPeerWorker unit d.clearWorkQueue)) tail


end Leanux.Proofs.WG.Index
