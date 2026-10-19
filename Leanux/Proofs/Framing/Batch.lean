import Leanux.Env.Batch
import Leanux.Proofs.Framing.Product
import Leanux.Proofs.WG.Packets.Primitives
import Leanux.Proofs.WG.Peers.Primitives

/-! Product frames over the original 43 store observations. Arbitrary worker
and filter callbacks retain their scope. These frames make no access claim. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Lifetimes

/-- A callback frame lifts through actual section records and NET_RX metadata. -/
theorem runWorker_sameView {σ : Type} (view : World → σ)
    (hv : ∀ w v, productStoreView v = productStoreView w → view v = view w)
    (worker : Worker) (body : Leanux.M Unit)
    (hb : SameView view body) : SameView view (Env.runWorker worker body) := by
  have ha {α : Type} (a : AmbientM α) : SameView view (monadLift a : Leanux.M α) :=
    fun initial => productAmbient_spec a (fun w => view w = initial)
      (fun w ambient hp => (hv w {w with ambient} rfl).trans hp)
  unfold Env.runWorker
  apply SameView.bind (ha (AmbientM.hidden (.sectionStart worker)))
  intro _
  by_cases hw : (worker == .netRx) = true
  · simp only [hw, ite_true]
    apply SameView.bind (ha (_root_.modify (fun s => {s with netRxSection := s.netRxSections})))
    intro _
    apply SameView.bind hb
    intro _
    apply SameView.bind (ha (_root_.modify (fun s => {s with netRxSection := 0})))
    intro _
    exact SameView.bind (ha (AmbientM.hidden (.sectionStop worker))) (fun _ => SameView.pure view ())
  · simp only [hw]
    exact SameView.bind hb (fun _ =>
      SameView.bind (ha (AmbientM.hidden (.sectionStop worker))) (fun _ => SameView.pure view ()))

theorem condResched_sameKernel (self : Worker) : SameProductStore (Env.condResched self) := by
  have ha {α : Type} (a : AmbientM α) : SameProductStore (monadLift a : Leanux.M α) :=
    fun initial => productAmbient_spec a (fun w => productStoreView w = initial) (fun _ _ hp => hp)
  unfold Env.condResched
  split
  · apply SameView.bind (ha AmbientM.peekHiddenSite)
    intro site
    split
    · exact SameView.pure _ _
    · exact SameView.bind (ha (AmbientM.hidden _)) (fun _ => SameView.pure _ _)
  · exact ha (AmbientM.invariant _)

/-- The actual trial runs on a copied product World. Its state is discarded;
hidden mismatches return false and every other Stop propagates. -/
theorem activationConsistent_sameKernel (a : Activation) :
    SameProductStore (Env.Activation.consistent a) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w b v hr
  unfold Env.Activation.consistent at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  cases he : (Env.Activation.run a).run w with
  | ok out =>
    simp only [he, StateT.run_pure] at hr
    cases hr
    rfl
  | error e =>
    simp only [he] at hr
    cases e <;> cases hr <;> rfl

theorem filterAuxM_sameKernel {S σ α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] (view : S → σ)
    (f : α → StateT S m Bool) (hf : ∀ a, SameView view (f a))
    (xs acc : List α) : SameView view (List.filterAuxM f xs acc) := by
  induction xs generalizing acc with
  | nil => exact SameView.pure view _
  | cons a xs ih => exact SameView.bind (hf a) (fun b => ih (cond b (a :: acc) acc))

theorem filterM_sameKernel {S σ α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] (view : S → σ)
    (f : α → StateT S m Bool) (hf : ∀ a, SameView view (f a))
    (xs : List α) : SameView view (xs.filterM f) :=
  SameView.bind (filterAuxM_sameKernel view f hf xs []) (fun ys => SameView.pure view ys.reverse)

theorem activationOccupancy_sameKernel (a : Activation) :
    SameProductStore (Env.Activation.occupancy a) := by
  have dev : SameWGStore WG.getDev := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient d v ambient' hr
    cases hd : w.dev <;> simp [WG.getDev, hd, invariant, AmbientM.invariant] at hr
    · cases hr
    · rcases hr with ⟨⟨_, rfl⟩, _⟩
      rfl
  have peer (pid : PeerId) : SameWGStore (getPeer pid) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' hr
    rw [(Leanux.Proofs.WG.Peers.getPeer_current pid w v p ambient ambient' hr).1]
  have hd := liftWG_sameProductStore WG.getDev dev
  have hp := fun pid => liftWG_sameProductStore (getPeer pid) (peer pid)
  have ha {α : Type} (x : AmbientM α) : SameProductStore (monadLift x : Leanux.M α) :=
    fun initial => productAmbient_spec x
      (fun w => productStoreView w = initial) (fun _ _ h => h)
  unfold Env.Activation.occupancy
  apply SameView.bind hd
  intro d
  cases a.worker <;> dsimp only <;> first
    | exact SameView.pure _ _
    | exact ha (AmbientM.invariant _)
    | skip
  split
  · exact SameView.bind (hp _) (fun _ => SameView.pure _ _)
  · exact ha (AmbientM.invariant _)

theorem activationHasWork_sameKernel (a : Activation) :
    SameProductStore (Env.Activation.hasWork a) := by
  have dev : SameWGStore WG.getDev := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient d v ambient' hr
    cases hd : w.dev <;> simp [WG.getDev, hd, invariant, AmbientM.invariant] at hr
    · cases hr
    · rcases hr with ⟨⟨_, rfl⟩, _⟩
      rfl
  have peer (pid : PeerId) : SameWGStore (getPeer pid) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' hr
    rw [(Leanux.Proofs.WG.Peers.getPeer_current pid w v p ambient ambient' hr).1]
  have packet (id : SkbId) : SameWGStore (getTxSkb id) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro g ambient p g' ambient' hr
    rw [(Leanux.Proofs.WG.Packets.getTxSkb_current id g g' p ambient ambient' hr).1]
  have hd := liftWG_sameProductStore WG.getDev dev
  have hp := fun pid => liftWG_sameProductStore (getPeer pid) (peer pid)
  have ht := fun id => liftWG_sameProductStore (getTxSkb id) (packet id)
  have ha {α : Type} (x : AmbientM α) : SameProductStore (monadLift x : Leanux.M α) :=
    fun initial => productAmbient_spec x
      (fun w => productStoreView w = initial) (fun _ _ h => h)
  unfold Env.Activation.hasWork
  apply SameView.bind hd
  intro d
  cases a.worker <;> dsimp only <;> first
    | exact SameView.pure _ _
    | exact ha (AmbientM.invariant _)
    | skip
  split
  · apply SameView.bind (hp _)
    intro p
    split
    · split
      · exact SameView.bind (ht _) (fun _ => SameView.pure _ _)
      · exact ha (AmbientM.invariant _)
    · exact SameView.pure _ _
  · exact ha (AmbientM.invariant _)

end Leanux.Proofs.Framing
