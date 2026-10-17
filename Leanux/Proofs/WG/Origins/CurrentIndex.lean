import Leanux.Proofs.WG.Origins.CurrentIdentity
import Leanux.Proofs.WG.Origins.IndexMaterial

/-! Exact peer identities through nullable index owner acquisition.
Only the two immutable peer fields are projected; owner words may be cleared.
Normal native endpoints retain receiving material with no affiliation premise. -/
namespace Leanux.Proofs.WG.CurrentIdentity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes

def peerView (w : WGWorld) : Option (PeerId → Option (Nat × Key)) :=
  w.dev.map fun d => fun pid => (d.peers[pid]?).map identity

theorem peerView_of_configured {α : Type} {a : WG.M α}
    (ha : SameView ConfiguredIdentity.view a) : SameView peerView a := by
  apply ha.of_factor (fun s => s.map fun s => fun pid =>
    (s.peers pid).map fun c => (c.stamp,c.static))
  intro w
  simp only [peerView,ConfiguredIdentity.view,ConfiguredIdentity.state,
    ConfiguredIdentity.cell,Option.map_map,Function.comp_def]
  rfl

theorem retains_of_peer_view (hm : Origins.Retains w v) (hv : peerView v = peerView w) :
    Retains w v := by
  intro d hd id key hk valid
  obtain ⟨keys,old,hw,ho,vo,kle⟩ := hm d.ifindex (fun q => d.keypairs[q]?)
    (by simp [Origins.view,hd]) id key hk valid
  obtain ⟨before,hb,fields⟩ := Option.map_eq_some_iff.mp hw
  have epoch : before.ifindex = d.ifindex := congrArg Prod.fst fields
  have oldKey := congrFun (congrArg Prod.snd fields) id
  have peers : (fun pid : PeerId => (d.peers[pid]?).map identity) =
      (fun pid : PeerId => (before.peers[pid]?).map identity) := by
    simpa only [peerView,hd,hb,Option.map_some,Option.some.injEq] using hv
  refine ⟨before,old,hb,epoch,oldKey.trans ho,vo,kle,?_⟩
  intro pid peer _ hp
  have previous : (before.peers[pid]?).map identity = some (identity peer) := by
    rw [← congrFun peers pid,hp]
    rfl
  obtain ⟨p,resident,same⟩ := Option.map_eq_some_iff.mp previous
  exact ⟨p,resident,same.symm⟩

theorem setPeerWord_peerView (owner : IndexOwner) (word : Option PeerId) :
    SameView peerView (owner.setPeerWord word) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  cases result
  cases owner with
  | keypair kid =>
    obtain ⟨d,k,hd,_,hv,_⟩ := Origins.keypair_word_store kid word w v ambient ambient' hr
    simp only [hv,CounterWindow.store,hd,peerView,Option.map_some]
  | handshake pid =>
    have hv := ConfiguredIdentity.word_effect pid word w v ambient ambient' hr
    have projected := congrArg (fun s => s.map fun s => fun q =>
      (s.peers q).map fun c => (c.stamp,c.static)) hv
    change peerView v = peerView w
    simp only [ConfiguredIdentity.view,ConfiguredIdentity.state,
      ConfiguredIdentity.cell,ConfiguredIdentity.State.setWord,
      apply_ite,Option.map_map,Function.comp_def,ite_self] at projected
    exact projected

theorem acquireOwner_peerView (owner : IndexOwner) :
    SameView peerView (Affiliation.acquireOwner owner) := by
  unfold Affiliation.acquireOwner
  apply SameView.bind (fun initial =>
    indexOwner_peerWord_preserves owner (fun w => peerView w = initial))
  intro word
  apply SameView.bind (peerView_of_configured (ConfiguredIdentity.peerGetMaybeZero_view word))
  intro borrowed
  apply SameView.bind (setPeerWord_peerView owner borrowed)
  intro _
  exact SameView.pure _ _

theorem acquireOwner_current (owner : IndexOwner) :
    ProjectedAction id Retains (Affiliation.acquireOwner owner) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  exact retains_of_peer_view
    ((ProjectedAction.iff_run_ambient _ _ _).mp (Origins.acquireOwner_retains owner)
      w ambient result v ambient' hr)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (acquireOwner_peerView owner)
      w ambient result v ambient' hr)

theorem indexLookup_peerView (kinds : List IndexKind) (index : Nat) :
    SameView peerView (indexLookup kinds index) := by
  intro initial
  let P := fun w => peerView w = initial
  have hb (decision : Decision) (value : Bool) : Preserves P (branch decision value) :=
    hoare_liftAmbient (AmbientM.branch decision value) P
  have stop {α : Type} (message : String) : Preserves P (invariant message : WG.M α) :=
    hoare_liftAmbient (AmbientM.invariant message) P
  have hi : Preserves P (liftIndex (indexBucket index)) := by
    apply hoare_liftIndex
    intro g d table hg hd
    simpa only [P,peerView,hd,Option.map_some] using hg
  have ha := fun owner => (acquireOwner_peerView owner).wp (fun p => p = initial)
  rw [← Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  repeat' first
    | (index_material_head branch; exact hb _ _)
    | (index_material_head invariant; exact stop _)
    | (index_material_head liftIndex; exact hi)
    | (index_material_head Affiliation.acquireOwner; exact ha _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply hoare_bind (Q := fun _ => P))
    | (index_material_head ForIn.forIn; apply list_view_spec peerView (fun p => p = initial))
    | dsimp (config := {failIfUnchanged := true}) only
    | (run_tac do
        let ty ← (← Lean.Elab.Tactic.getMainGoal).getType
        unless ty.isForall do Lean.throwError "not a binder"
        Lean.Elab.Tactic.evalTactic (← `(tactic| intro x)))
    | split

/-- Normal None after a failed get is covered, as is a cleared owner word.
Missing-object and other Stops supply no returned state. -/
theorem indexLookup_current (kinds : List IndexKind) (index : Nat) :
    ProjectedAction id Retains (indexLookup kinds index) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  exact retains_of_peer_view
    ((ProjectedAction.iff_run_ambient _ _ _).mp (Origins.indexLookup_retains kinds index)
      w ambient result v ambient' hr)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (indexLookup_peerView kinds index)
      w ambient result v ambient' hr)

end Leanux.Proofs.WG.CurrentIdentity

namespace Leanux.Proofs.WG.ConfiguredIdentity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes

/-- The literal index scan preserves configured-table identity even when a
normal failed acquisition clears its owner word. No affiliation premise is
needed; the existing self-word invariant is transported by acquisition. -/
theorem indexLookup_preserves (kinds : List IndexKind) (index : Nat) :
    Preserves Inv (indexLookup kinds index) := by
  change Hoare (indexLookup kinds index) Inv (fun _ => Inv)
  have hb (decision : Decision) (value : Bool) : Preserves Inv (branch decision value) :=
    hoare_liftAmbient (AmbientM.branch decision value) Inv
  have stop {α : Type} (message : String) : Preserves Inv (invariant message : WG.M α) :=
    hoare_liftAmbient (AmbientM.invariant message) Inv
  have hi : Preserves Inv (liftIndex (indexBucket index)) := by
    apply hoare_liftIndex
    intro g d table hg hd
    simpa only [Inv,InvExcept,view,hd,Option.map_some,state] using hg
  have ha (owner : IndexOwner) : Preserves Inv (Affiliation.acquireOwner owner) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v ambient' hw hr
    exact acquireOwner_preserves owner w v result ambient ambient' hw hr
  rw [← Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  repeat' first
    | (index_material_head branch; exact hb _ _)
    | (index_material_head invariant; exact stop _)
    | (index_material_head liftIndex; exact hi)
    | (index_material_head Affiliation.acquireOwner; exact ha _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply hoare_bind (Q := fun _ => Inv))
    | (index_material_head ForIn.forIn; apply list_view_spec id Inv)
    | dsimp (config := {failIfUnchanged := true}) only
    | (run_tac do
        let ty ← (← Lean.Elab.Tactic.getMainGoal).getType
        unless ty.isForall do Lean.throwError "not a binder"
        Lean.Elab.Tactic.evalTactic (← `(tactic| intro x)))
    | split

end Leanux.Proofs.WG.ConfiguredIdentity
