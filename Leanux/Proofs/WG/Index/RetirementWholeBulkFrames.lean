import Leanux.Proofs.WG.Index.RetirementFirstPassSource
import Leanux.Proofs.WG.Index.OwnerCoherenceAipRemovalSource
import Leanux.Proofs.WG.Index.HashSlotLookupFrames
import Leanux.Proofs.WG.Index.RetirementSavedCleanupSource
import Leanux.Proofs.WG.Index.RetirementSendAdapterSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

/-- The existing allowed-IP observation retains every field used by hashed
slot coverage and positive owner coherence. No tracked resident is required. -/
theorem aipOwnerView_hashSlots_coherent (d final : Device)
    (same : aipOwnerView final = aipOwnerView d)
    (covered : HashSlotCoverage d) (coherent : HashedOwnersCoherent d) :
    HashSlotCoverage final ∧ HashedOwnersCoherent final := by
  have table : final.indexTable = d.indexTable := congrArg Prod.fst same
  have keys : final.keypairs = d.keypairs := congrArg (fun x => x.2.1) same
  have peers := congrArg (fun x => x.2.2.1) same
  dsimp only [aipOwnerView] at peers
  constructor
  · apply hashSlotCoverage_transport d final table _ _ covered
    · intro pid
      have cell := congrArg (Option.map clearKeys) (congrFun peers pid)
      change (final.peers[pid]?.map fun p => [p.keypairNext,p.keypairPrevious,p.keypairCurrent]) =
        (d.peers[pid]?.map fun p => [p.keypairNext,p.keypairPrevious,p.keypairCurrent])
      simpa only [Option.map_map,Function.comp_def,aipOwnerPeer,clearKeys] using cell
    · intro kid
      rw [keys]
  · intro entry member
    obtain ⟨pid,p,word,resident,positive,kind⟩ := coherent entry (table ▸ member)
    exact (aipOwnerView_transport d final pid p same resident coherent
      (hashSlotCoverage_lastOwnerCovered d pid p resident coherent covered)).1 entry member

/-- Projection of the landed complete allowed-IP clear effect. Trie nodes
and each allowed-IP list are the only discarded data. -/
theorem free_aipOwnerView :
    SameView (fun w : WGWorld => w.dev.map aipOwnerView) WG.free := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  have effect := (hoare_iff_run_ambient _ _ _).mp
    (AllowedIps.free_storeView (wgStoreView w)) w a value v b rfl run
  let project (s : WGStoreView × (PeerId → Option Peer)) :=
    s.1.dev.map fun d => (d.indexTable,d.keypairs,s.2,d.numPeers,
      d.sendWorkQueue,d.clearWorkQueue)
  have projected := congrArg project effect
  have left : project (AllowedIps.clearStoreView v) = v.dev.map aipOwnerView := by
    cases device : v.dev <;>
      simp only [project,AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,
        wgStoreView,device,Option.map_none,Option.map_some,Option.bind_none,Option.bind_some]
    rfl
  have right : project (AllowedIps.clearStoreProjection
      {wgStoreView w with dev := w.dev.map AllowedIps.resetAllowedips}) =
      w.dev.map aipOwnerView := by
    cases device : w.dev <;>
      simp only [project,AllowedIps.clearStoreProjection,wgStoreView,
        Option.map_none,Option.map_some,Option.bind_none,Option.bind_some]
    rfl
  exact left.symm.trans (projected.trans right)

/-- Actual allowed-IP free retains both index relations on every normal
return, with no trie-shape or successful-execution premise. -/
theorem free_hashSlots_coherent :
    Preserves (fun w : WGWorld => ∀ d, w.dev = some d →
      HashSlotCoverage d ∧ HashedOwnersCoherent d) WG.free := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b pre run final out
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp free_aipOwnerView
    w a value v b run
  cases device : w.dev with
  | none => simp [device,out] at same
  | some d =>
    have fields : aipOwnerView final = aipOwnerView d := by simpa [device,out] using same
    exact aipOwnerView_hashSlots_coherent d final fields (pre d device).1 (pre d device).2

/-- Whole original dead marking retains all hashed slots and owner counts.
The rich owned removal frame is reused; only the existing final paired
read/write cut is inspected, preserving its original missing-peer refusal. -/
theorem peerMakeDead_hashSlots_coherent (pid : PeerId) :
    Preserves (fun w : WGWorld => ∀ d, w.dev = some d →
      HashSlotCoverage d ∧ HashedOwnersCoherent d) (peerMakeDead pid) := by
  apply (ensures_iff _ _ _).mp
  let P := fun w : WGWorld => ∀ d, w.dev = some d →
    HashSlotCoverage d ∧ HashedOwnersCoherent d
  have unlist : Ensures (modifyDev (Config.unlistPeer · pid)) P (fun _ => P) := by
    intro w a result v b pre run final out
    cases run
    cases device : w.dev with
    | none => simp [device] at out
    | some d =>
      have eq : final = Config.unlistPeer d pid := by
        simpa [modifyDev,device] using out.symm
      subst final
      exact pre d device
  have remove : Ensures (removeByPeer pid) P (fun _ => P) := by
    intro w a result v b pre run final out
    have same := removeByPeer_spec_aipOwner_variant pid (w.dev.map aipOwnerView)
      w a result v b rfl run
    cases device : w.dev with
    | none => simp [device,out] at same
    | some d =>
      have fields : aipOwnerView final = aipOwnerView d := by simpa [device,out] using same
      exact aipOwnerView_hashSlots_coherent d final fields (pre d device).1 (pre d device).2
  have mark : Ensures (Config.makeDeadAfterRemoval pid) P (fun _ => P) := by
    intro w a result v b pre run final out
    cases device : w.dev with
    | none =>
      simp [Config.makeDeadAfterRemoval,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.peers[pid]? with
      | none =>
        simp [Config.makeDeadAfterRemoval,getDev,device,branch,AmbientM.branch,
          modifyDev,getPeer,resident,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        let unlinked := {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)}
        let marked := {p with isDead := true}
        let next := Config.withPeer unlinked pid marked
        have actual : ((Config.makeDeadAfterRemoval pid).run w).run a =
            .ok (((),{w with dev := some next}),
              {a with steps := a.steps.push {
                decision := .pubkeyRemoveHashed,
                outcome := d.peerHashtable.any (·.2 == pid),
                netRx := a.netRxSection}}) := by
          simp [Config.makeDeadAfterRemoval,getDev,device,branch,AmbientM.branch,
            modifyDev,getPeer,setPeer,resident,next,unlinked,marked,Config.withPeer]
        rw [actual] at run
        have stateEq : {w with dev := some next} = v :=
          congrArg (fun result => result.1.2) (Except.ok.inj run)
        rw [← stateEq] at out
        have finalEq : final = next := Option.some.inj out.symm
        subst final
        exact ⟨hashSlotCoverage_peerWrite unlinked pid p marked resident rfl (pre d device).1,
          peerWrite_owner_coherent unlinked pid p marked resident rfl rfl (pre d device).2⟩
  rw [Config.peerMakeDead_source]
  exact ensures_bind _ _ unlist (fun _ => ensures_bind _ _ remove (fun _ => mark))

end Leanux.Proofs.WG.Index
