import Leanux.Proofs.WG.Index.AipRemovalFrames
import Leanux.Proofs.WG.Config.ReadbackSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- On normal return, actual arbitrary-state allowed-IP removal preserves the
getter socket and fixture selector through guarded Aip lifts and captured list mutations.
This reuses the owned guarded adapter; no trie shape or completion premise. -/
theorem removeByPeer_readbackFrame (pid : PeerId) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (removeByPeer pid) (fun g => readbackFrame g sock fixtures)
      (fun _ g => readbackFrame g sock fixtures) := by
  let P : WGWorld → Prop := fun g => readbackFrame g sock fixtures
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g a result final after pre run
    cases run
    exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have haip {α : Type} (action : AipM α) :
      Ensures (liftM action : WG.M α) P (fun _ => P) := by
    change Ensures (liftAip action) P (fun _ => P)
    apply (ensures_iff _ _ _).mpr (Index.hoare_liftAip_variant action P ?_)
    intro g d store pre device
    exact pre
  have hpeer (id : PeerId) : Ensures (getPeer id) P (fun _ => P) := by
    intro g a result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec id P) g a result final after pre run).1
  have hmodify (f : Device → Device) : Ensures (modifyDev f) P (fun _ => P) := by
    intro g a result final after pre run
    cases run
    exact pre
  have hget : Ensures getDev P (fun _ => P) := by
    intro g a result final after pre run
    cases device : g.dev with
    | none =>
      simp [getDev,device] at run
      change Except.error (Stop.invariant "no WireGuard device in this trace's fixture") =
        .ok ((result,final),after) at run
      cases run
    | some d =>
      simp [getDev,device] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      exact pre
  have hlistDel (id : NodeId) : Ensures (listDel id) P (fun _ => P) := by
    have entries (items : List (PeerId × Peer)) :
        Ensures (listDelEntries id items) P (fun _ => P) := by
      induction items with
      | nil => exact hpure ()
      | cons item rest ih =>
        rcases item with ⟨pid,p⟩
        rw [listDelEntries_cons]
        split
        · exact ensures_bind (Q := fun _ => P) _ _ (hmodify _) (fun _ => ih)
        · exact ih
    rw [listDel_source]
    exact ensures_bind (Q := fun _ => P) _ _ hget (fun d => entries d.peers.toList)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    hambient (AmbientM.branch site value)
  have hbit (n : AipNode) (bit : Nat) : Ensures (n.bitAt bit : WG.M (Option NodeId)) P (fun _ => P) := by
    unfold AipNode.bitAt
    split
    · exact hpure _
    · exact hambient (AmbientM.invariant _)
  have hinv {α : Type} (what : String) : Ensures (invariant what : WG.M α) P (fun _ => P) :=
    hambient (AmbientM.invariant what)
  have hnode (id : NodeId) (n : AipNode) :
      Ensures (removeNodeSource id n) P (fun _ => P) := by
    unfold removeNodeSource
    repeat' first
      | (with_reducible exact hpure _)
      | (with_reducible exact haip _)
      | (with_reducible exact hbit _ _)
      | (with_reducible exact hbranch _ _)
      | (with_reducible exact hinv _)
      | (with_reducible refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
      | split
  have hlist {α β : Type} (xs : List α) (initial : β)
      (body : α → β → WG.M (ForInStep β))
      (step : ∀ a b, Ensures (body a b) P (fun _ => P)) :
      Ensures (forIn xs initial body) P (fun _ => P) := by
    induction xs generalizing initial with
    | nil => simpa only [List.forIn_nil] using hpure initial
    | cons x xs ih =>
      rw [List.forIn_cons]
      refine ensures_bind _ _ (step x initial) ?_
      intro result
      cases result with
      | done final => exact hpure final
      | yield next => exact ih next
  rw [removeByPeer_source]
  refine ensures_bind (Q := fun _ => P) _ _ (hpeer pid) ?_
  intro p
  rw [removeByPeer_factor]
  unfold removeByPeerFactored
  refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
  intro empty
  cases empty with
  | true => exact hpure ()
  | false =>
    refine ensures_bind (Q := fun _ => P) _ _ (hmodify _) ?_
    intro _
    refine ensures_bind (Q := fun _ => P) _ _ (hlist _ _ _ ?_) ?_
    · intro id accumulator
      refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
      intro _
      refine ensures_bind (Q := fun _ => P) _ _ (hlistDel id) ?_
      intro _
      refine ensures_bind (Q := fun _ => P) _ _ (haip (getNode id)) ?_
      exact hnode id
    · intro _
      refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
      intro _
      exact hpure ()

end Leanux.Proofs.WG.Config
