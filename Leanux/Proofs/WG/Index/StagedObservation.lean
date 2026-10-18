import Lean.Elab.Tactic
import Leanux.Proofs.WG.Index.ConsumeFrames
import Leanux.Proofs.WG.Config.StagedSource
import Leanux.Proofs.WG.Config.KeyReferences
import Leanux.Proofs.WG.Index.SendSource
import Leanux.Proofs.WG.Noise.ClearWorkerFrames
import Leanux.Proofs.WG.Noise.TagCoverageModel
import Leanux.Proofs.WG.Keypairs.Frames.WGTransitions

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- A surviving peer retains both its response tag and optional pending slot. -/
abbrev stagingPeerCell (p : Peer) := (p.handshakeState, p.keypairNext)

def stagingPeerMap (device : Option Device) (pid : PeerId) :=
  (device.bind fun d => d.peers[pid]?).map stagingPeerCell

def StagingPeersRetained (entry current : WGWorld) : Prop :=
  ∀ pid cell, stagingPeerMap current.dev pid = some cell →
    stagingPeerMap entry.dev pid = some cell

def TagRetained (entry current : WGWorld) : Prop :=
  TagsRetained (responseTagMap entry.dev) (responseTagMap current.dev)

/-- Fixed-entry table implication, surviving peer cells and the global key
allocation frontier. No initially safe table is required for the latter facts. -/
def StagingFrame (entry current : WGWorld) : Prop :=
  (TablesSafeWG entry → TablesSafeWG current) ∧
  StagingPeersRetained entry current ∧ current.keypairCounter = entry.keypairCounter

theorem stagingFrame_refl (entry : WGWorld) : StagingFrame entry entry :=
  ⟨fun h => h, (fun _ _ h => h), rfl⟩

theorem stagingPeerMap_tags (device : Option Device) (pid : PeerId) :
    responseTagMap device pid = (stagingPeerMap device pid).map Prod.fst := by
  simp [responseTagMap,stagingPeerMap,Option.map_map,Function.comp_def]

theorem stagingPeerMap_write (d : Device) (pid : PeerId) (p q : Peer)
    (resident : d.peers[pid]? = some p) (cell : stagingPeerCell q = stagingPeerCell p) :
    stagingPeerMap (some {d with peers := d.peers.insert pid q}) = stagingPeerMap (some d) := by
  funext target
  by_cases same : pid = target
  · subst target
    simp [stagingPeerMap,resident,cell]
  · simp [stagingPeerMap,Std.TreeMap.getElem?_insert,same]

theorem staging_counter_snapshot {α : Type} (action : WG.M α)
    (frame : Keypairs.SameSnapshot action) (g final : WGWorld)
    (ambient after : Ambient) (result : α)
    (run : ((action.run g).run ambient = .ok ((result,final),after))) :
    final.keypairCounter = g.keypairCounter :=
  congrArg Keypairs.Snapshot.frontier
    ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp frame
      g ambient result final after run)

theorem staging_read_bind (entry : WGWorld) (pid : PeerId) {α : Type}
    (next : Peer → WG.M α) (Q : α → WGWorld → Prop)
    (body : ∀ p, stagingPeerMap entry.dev pid = some (stagingPeerCell p) →
      Ensures (next p) (StagingFrame entry) Q) :
    Ensures (getPeer pid >>= next) (StagingFrame entry) Q := by
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (getPeer_spec pid (StagingFrame entry))) ?_
  intro p g ambient result final after pre run
  have observed : stagingPeerMap g.dev pid = some (stagingPeerCell p) := by
    change (peerAt g pid).map stagingPeerCell = _
    rw [pre.2]
    rfl
  exact body p (pre.1.2.1 pid (stagingPeerCell p) observed)
    g ambient result final after pre.1 run

theorem staging_setPeer (entry : WGWorld) (pid : PeerId) (p : Peer)
    (cell : stagingPeerMap entry.dev pid = some (stagingPeerCell p)) :
    Ensures (setPeer pid p) (StagingFrame entry) (fun _ => StagingFrame entry) := by
  intro g ambient result final after pre run
  have tables := (ensures_iff _ _ _).mpr (setPeer_tables pid p)
  refine ⟨fun h => tables g ambient result final after (pre.1 h) run, ?_, ?_⟩
  · cases run
    intro target t present
    cases device : g.dev with
    | none => simp [stagingPeerMap,device] at present
    | some d =>
      by_cases same : pid = target
      · subst target
        simp only [stagingPeerMap,device,Option.map_some,Option.bind_some,
          Std.TreeMap.getElem?_insert_self,Option.map_some,Option.some.injEq] at present
        subst t
        exact cell
      · apply pre.2.1 target t
        simpa [stagingPeerMap,device,Std.TreeMap.getElem?_insert,same] using present
  · cases run
    exact pre.2.2

theorem staging_of_same_peers {α : Type} (entry : WGWorld) (action : WG.M α)
    (tables : Ensures action TablesSafeWG (fun _ => TablesSafeWG))
    (peers : ∀ g ambient result final after,
      ((action.run g).run ambient = .ok ((result,final),after)) →
      stagingPeerMap final.dev = stagingPeerMap g.dev ∧
      final.keypairCounter = g.keypairCounter) :
    Ensures action (StagingFrame entry) (fun _ => StagingFrame entry) := by
  intro g ambient result final after pre run
  have same := peers g ambient result final after run
  refine ⟨fun h => tables g ambient result final after (pre.1 h) run, ?_, same.2.trans pre.2.2⟩
  intro pid cell resident
  apply pre.2.1 pid cell
  rw [← same.1]
  exact resident

theorem staging_tables {α : Type} (action : WG.M α)
    (framed : ∀ entry, Ensures action (StagingFrame entry) (fun _ => StagingFrame entry)) :
    Ensures action TablesSafeWG (fun _ => TablesSafeWG) := by
  intro g ambient result final after pre run
  exact (framed g g ambient result final after (stagingFrame_refl g) run).1 pre

theorem staging_tags {α : Type} (action : WG.M α)
    (framed : ∀ entry, Ensures action (StagingFrame entry) (fun _ => StagingFrame entry)) :
    ∀ g ambient result final after,
      ((action.run g).run ambient = .ok ((result,final),after)) → TagRetained g final := by
  intro g ambient result final after run pid tag present
  have retained := (framed g g ambient result final after (stagingFrame_refl g) run).2.1
  rw [stagingPeerMap_tags] at present ⊢
  cases cell : stagingPeerMap final.dev pid with
  | none => simp [cell] at present
  | some pair =>
    rw [retained pid pair cell]
    simpa [cell] using present

theorem stagingFrame_of_views (entry g final : WGWorld)
    (cursor : final.dev.map TimerDiscipline.tableCursor = g.dev.map TimerDiscipline.tableCursor)
    (peers : stagingPeerMap final.dev = stagingPeerMap g.dev)
    (counter : final.keypairCounter = g.keypairCounter)
    (pre : StagingFrame entry g) : StagingFrame entry final := by
  refine ⟨fun safe => tablesSafe_of_cursor g final cursor (pre.1 safe), ?_, counter.trans pre.2.2⟩
  intro pid cell present
  exact pre.2.1 pid cell (by rw [← peers]; exact present)

theorem staging_modifyDev (entry : WGWorld) (f : Device → Device)
    (cursor : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
    (peers : ∀ d, (f d).peers = d.peers) :
    Ensures (modifyDev f) (StagingFrame entry) (fun _ => StagingFrame entry) := by
  intro g ambient result final after pre run
  cases run
  refine ⟨fun h => tablesSafe_of_cursor g _
    (by simp [Option.map_map,Function.comp_def,cursor]) (pre.1 h), ?_, pre.2.2⟩
  intro pid cell present
  apply pre.2.1 pid cell
  simpa only [stagingPeerMap,Option.bind_map,Function.comp_def,peers] using present

theorem staging_indexRemove (entry : WGWorld) (owner : IndexOwner) :
    Ensures (liftIndex (indexRemove owner)) (StagingFrame entry)
      (fun _ => StagingFrame entry) := by
  apply staging_of_same_peers entry _
    ((ensures_iff _ _ _).mpr (indexRemove_tables owner))
  intro g ambient result final after run
  exact (ensures_iff _ _ _).mpr
    (hoare_liftIndex_variant (indexRemove owner)
      (fun w => stagingPeerMap w.dev = stagingPeerMap g.dev ∧ w.keypairCounter = g.keypairCounter)
      (by
        intro w d table pre device
        constructor
        · change stagingPeerMap (some d) = _
          simpa [device] using pre.1
        · exact pre.2))
    g ambient result final after ⟨rfl,rfl⟩ run

theorem staging_peerPut (entry : WGWorld) (peer : Option PeerId) :
    Ensures (peerPut peer) (StagingFrame entry) (fun _ => StagingFrame entry) := by
  intro g ambient result final after pre run
  refine ⟨fun h => (ensures_iff _ _ _).mpr (peerPut_tables peer)
    g ambient result final after (pre.1 h) run, ?_, ?_⟩
  · cases peer with
    | none =>
      simp [peerPut,branch,AmbientM.branch] at run
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
      exact pre.2.1
    | some pid =>
      cases device : g.dev with
      | none =>
        simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,
          device,invariant,AmbientM.invariant] at run
        cases run
      | some d =>
        cases resident : d.peers[pid]? with
        | none =>
          simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,
            device,resident,invariant,AmbientM.invariant] at run
          cases run
        | some p =>
          by_cases zero : p.refcount = 0
          · simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,
              device,resident,zero,refcountDecAndTest,branchCmp,AmbientM.branchCmp,
              invariant,AmbientM.invariant] at run
            cases run
          · have live : 0 < p.refcount := by omega
            have effect := peerPut_exact pid d p resident live g ambient device
            change (match peerReleaseRefusal pid p with
              | some stop => Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) = .error stop
              | none => ∃ s, Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) =
                .ok ((), s) ∧ s.wg.device = some (releasedPeerDevice d pid p)) at effect
            rw [run] at effect
            cases refused : peerReleaseRefusal pid p with
            | some stop => simp [refused,Campaign2.observeResult,Except.map] at effect
            | none =>
              simp only [refused,Campaign2.observeResult,Except.map] at effect
              obtain ⟨s,equality,actual⟩ := effect
              cases equality
              change final.dev = some (releasedPeerDevice d pid p) at actual
              intro target cell present
              apply pre.2.1 target cell
              by_cases last : p.refcount = 1 <;> by_cases same : pid = target
              all_goals simp_all [stagingPeerMap,stagingPeerCell,releasedPeerDevice,
                Std.TreeMap.getElem?_erase,Std.TreeMap.getElem?_insert]
  · exact (staging_counter_snapshot _ (Keypairs.WGFrames.peerPut_sameSnapshot peer)
      g final ambient after result run).trans pre.2.2

open Lean Meta Elab Tactic in
/-- Select the actual getter bind before the generic bind rule forgets the
returned peer's tag. This tactic only selects syntax; the kernel checks read_bind. -/
elab "staging_getPeer_bind" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Ensures do throwError "not an Ensures contract"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let binds := action.getAppArgs
  unless binds[binds.size - 2]!.consumeMData.isAppOf ``getPeer do
    throwError "not a getPeer bind"

end Leanux.Proofs.WG.Index
