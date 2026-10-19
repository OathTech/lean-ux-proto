import Leanux.Proofs.WG.Origins.CurrentIdentity
import Leanux.Proofs.WG.Origins.RetainingLifecycle

/-! Normal-return current identity transport through peer retirement.
Deletion is allowed; surviving peers retain both allocation stamp and static key.
No initialized history, affiliation, or positive-reference premise is assumed. -/
namespace Leanux.Proofs.WG.CurrentIdentity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes

private theorem retains_peer_fields (w v : WGWorld) (before : Device)
    (hw : w.dev = some before)
    (fields : ∀ after, v.dev = some after → before.ifindex = after.ifindex ∧
      after.keypairs = before.keypairs ∧
      ∀ (pid : PeerId) (p : Peer), after.peers[pid]? = some p →
        ∃ old, before.peers[pid]? = some old ∧ identity p = identity old) : Retains w v := by
  intro d hd id key hk valid
  obtain ⟨epoch, keys, peers⟩ := fields d hd
  refine ⟨before, key, hw, epoch, ?_, valid, Origins.KeyLe.refl _, ?_⟩
  · simpa only [keys] using hk
  · intro pid p _ hp
    exact peers pid p hp

/-- A successful peer payment may erase the resident peer. Every survivor
keeps its stamp and static key, including the nonfinal decrement case. -/
theorem peerPut_retains (peer : Option PeerId) :
    ProjectedAction id Retains (peerPut peer) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  cases result
  cases peer with
  | none =>
    simp [peerPut, branch, AmbientM.branch] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact Retains.refl _
  | some pid =>
    cases hd : w.dev with
    | none =>
      simp [peerPut, requireNotPending, getPeer, getDev, hd, branch, AmbientM.branch,
        invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [peerPut, requireNotPending, getPeer, getDev, hd, hp, branch, AmbientM.branch,
          invariant, AmbientM.invariant] at hr
        cases hr
      | some p =>
        have hl (a : IndexM Unit) : (liftM a : WG.M Unit) = liftIndex a := rfl
        by_cases positive : 0 < p.refcount
        · have nonzero : p.refcount ≠ 0 := by omega
          by_cases final : p.refcount = 1
          all_goals
            simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
              refcountDecAndTest, branch, branchCmp, indexRemove_eq, indexUnhash,
              hl, liftIndex_run, retirePeerUnits, modifyAmbient,
              CounterWindow.branch_run, CounterWindow.branchCmp_run,
              hd, hp, positive, nonzero, final,
              StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              CounterWindow.except_ok_bind, CounterWindow.except_pure,
              invariant, AmbientM.invariant, unsupported, AmbientM.unsupported] at hr
          all_goals repeat' first | split at hr | contradiction
          all_goals rcases hr with ⟨rfl, rfl⟩
          all_goals apply retains_peer_fields w _ d hd
          all_goals
            intro after ha
            cases ha
            refine ⟨rfl, rfl, ?_⟩
          all_goals
            intro q current resident
            by_cases eq : pid = q
            · subst q
              simp only [Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert,
                Std.LawfulEqOrd.compare_eq_iff_eq, ite_true] at resident
              first
                | contradiction
                | (cases resident; exact ⟨p, hp, rfl⟩)
            · exact ⟨current, by simpa [Std.TreeMap.getElem?_erase,
                Std.TreeMap.getElem?_insert, eq] using resident, rfl⟩
        · have zero : p.refcount = 0 := by omega
          simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
            refcountDecAndTest, hd, hp,
            branch, branchCmp, CounterWindow.branch_run, CounterWindow.branchCmp_run,
            zero, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
            CounterWindow.except_ok_bind, CounterWindow.except_pure,
            unsupported, AmbientM.unsupported] at hr
          cases hr

/-- Marking a peer dead removes its configuration row but does not replace
its allocation identity or static key. Trie edits retain those fields too. -/
theorem peerMakeDead_retains (pid : PeerId) :
    ProjectedAction id Retains (peerMakeDead pid) := by
  have frame {α : Type} (a : WG.M α)
      (hm : SameView Origins.view a) (hc : SameView ConfiguredIdentity.view a) :
      ProjectedAction id Retains a := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hr
    exact retains_of_configured_view
      ((ProjectedAction.iff_run_ambient _ _ _).mp (Origins.Retaining.of_view hm)
        w ambient x v ambient' hr)
      ((ProjectedAction.iff_run_ambient _ _ _).mp hc w ambient x v ambient' hr)
  have first : ProjectedAction id Retains
      (modifyDev fun d => {d with peerList := d.peerList.filter (· != pid)}) :=
    frame _ (Origins.Retaining.modifyDev_material _ (fun _ => rfl))
      (fun initial => ConfiguredIdentity.modifyDev_spec (fun s => s = initial) _ (fun _ => rfl))
  have remove : ProjectedAction id Retains (removeByPeer pid) :=
    frame _ (Origins.Retaining.removeByPeer_material pid) (ConfiguredIdentity.removeByPeer_view pid)
  have kill : ProjectedAction id Retains (ConfiguredIdentity.killRows pid) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hr
    cases x
    cases hd : w.dev with
    | none =>
      simp [ConfiguredIdentity.killRows, modifyDev, getPeer, getDev, hd,
        invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [ConfiguredIdentity.killRows, modifyDev, getPeer, getDev, hd, hp,
          invariant, AmbientM.invariant] at hr
        cases hr
      | some p =>
        simp [ConfiguredIdentity.killRows, modifyDev, getPeer, getDev, setPeer, hd, hp] at hr
        rcases hr with ⟨rfl, rfl⟩
        apply retains_peer_fields w _ d hd
        intro after ha
        cases ha
        refine ⟨rfl, rfl, ?_⟩
        intro q current resident
        by_cases eq : pid = q
        · subst q
          simp only [Std.TreeMap.getElem?_insert_self, Option.some.injEq] at resident
          subst current
          exact ⟨p, hp, rfl⟩
        · exact ⟨current, by simpa [Std.TreeMap.getElem?_insert, eq] using resident, rfl⟩
  have factor : peerMakeDead pid = (do
      modifyDev fun d => {d with peerList := d.peerList.filter (· != pid)}
      removeByPeer pid
      _ ← branch .pubkeyRemoveHashed ((← getDev).peerHashtable.any (·.2 == pid))
      ConfiguredIdentity.killRows pid) := rfl
  intro initial
  have keep {α : Type} {a : WG.M α} (ha : ProjectedAction id Retains a) :
      Preserves (Retains initial) a :=
    ha.wp (Retains initial) (fun _ _ h before => before.trans h)
  apply hoare_consequence (P := Retains initial) (Q := fun _ => Retains initial) ?_
    (fun w h => by change w = initial at h; subst w; exact Retains.refl _)
    (fun _ _ h => h)
  rw [factor]
  apply preserves_bind (keep first)
  intro _
  apply preserves_bind (keep remove)
  intro _
  have getter : Preserves (Retains initial) getDev := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient d v ambient' hi hr
    cases hd : w.dev with
    | none =>
      simp [getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some saved =>
      simp [getDev, hd] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact hi
  apply preserves_bind getter
  intro d
  apply preserves_bind (hoare_liftAmbient
    (AmbientM.branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid))) (Retains initial))
  intro _
  exact keep kill

end Leanux.Proofs.WG.CurrentIdentity
