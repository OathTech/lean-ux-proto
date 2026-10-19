import Leanux.Proofs.WG.Config.RequestWgChainEffects
import Leanux.Proofs.WG.Config.RequestRecordSource
import Leanux.Proofs.WG.Config.RequestOrderInspectionSource

/-! Actual peerBody/peers source composition with the existing remaining-list rule. Before-key fwmark transport reuses its completed-history contract; the original request factory supplies the rest. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder.WgLinks
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Leanux.Proofs.WG.Configuration

theorem mark_at (z : Ambient) (site : Decision) (value : Bool) :
    StatePrefixPreserves (fun h w _=>At h (Campaign2.snapshot w z).wg)
      Safe (mark site value) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ pre=>pre.safe)
  intro h g a result v b pre run
  have frame := (Internal.ambient_frame (AmbientM.branch site value)).bind
    (fun _=>SameView.pure (id : WGWorld→WGWorld) ())
  have same : v=g := (ProjectedAction.iff_run_ambient _ _ _).mp frame g a result v b run
  exact same ▸ pre

theorem pure_at {α : Type} (z : Ambient) (value : α) :
    StatePrefixPreserves (fun h w _=>At h (Campaign2.snapshot w z).wg)
      Safe (pure value : WGPrefix Receipt α) :=
  StatePrefixEnsures.pure value (fun _ _ _ pre=>pre.safe) (fun _ _ _ pre=>pre)

theorem peer_at (attrs : DeviceAttrs) (z : Ambient) (p : PeerAttrs) :
    StatePrefixPreserves (fun h w _=>At h (Campaign2.snapshot w z).wg)
      Safe (record attrs (.peer p)) := by
  apply record_state_rule attrs (.peer p) (fun _ _ _ pre=>pre.safe)
  intro h g a result v b pre run
  have next := pre.peer_append (receipt (.peer p) ⟨result,g,v,a,b⟩) p rfl rfl
  exact ⟨next.safe,next⟩

theorem peerBody_at (attrs : DeviceAttrs) (z : Ambient) (entry : PeerEntry)
    (out : Option Int×Unit) :
    StatePrefixPreserves (fun h w _=>At h (Campaign2.snapshot w z).wg)
      Safe (peerBody attrs entry out) := by
  unfold StatePrefixPreserves
  cases entry <;> simp only [peerBody,zero]
  all_goals
    repeat' first
      | (maintenance_head record; exact peer_at attrs z _)
      | (maintenance_head mark; exact mark_at z _ _)
      | (maintenance_head Pure.pure; exact pure_at z _)
      | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind)
      | (maintenance_intro; try dsimp only)
      | split

theorem peerLoop_at (attrs : DeviceAttrs) (z : Ambient) (xs : List PeerEntry)
    (out : Option Int×Unit) :
    StatePrefixPreserves (fun h w _=>At h (Campaign2.snapshot w z).wg)
      Safe (forIn xs out (peerBody attrs)) := by
  apply RemainingLoop.forIn_remaining xs out (peerBody attrs)
    (fun _ _ h w _=>At h (Campaign2.snapshot w z).wg)
  · exact fun _ _ _ _ pre=>pre.safe
  · exact fun _ _ _ _ pre=>⟨pre.safe,pre⟩
  · intro entry rest out
    exact (peerBody_at attrs z entry out).consequence (fun _ _ _ pre=>pre)
      (fun step _ _ _ pre=>by cases step <;> exact pre)

theorem peers_at (attrs : DeviceAttrs) (z : Ambient) :
    StatePrefixPreserves (fun h w _=>At h (Campaign2.snapshot w z).wg)
      Safe (peers attrs) := by
  unfold StatePrefixPreserves
  rw [peers_factor]
  unfold zero
  repeat' first
    | (maintenance_head ForIn.forIn; exact peerLoop_at attrs z _ _)
    | (maintenance_head mark; exact mark_at z _ _)
    | (maintenance_head Pure.pure; exact pure_at z _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind)
    | (maintenance_intro; try dsimp only)
    | split

theorem lift_before {α : Type} (action : WG.M α) :
    StatePrefixPreserves (fun h _ _=>Before h) Safe (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ pre=>pre.safe)
    (fun _ _ _ _ _ _ pre _=>pre)

theorem mark_before (site : Decision) (value : Bool) :
    StatePrefixPreserves (fun h _ _=>Before h) Safe (mark site value) :=
  lift_before _

theorem pure_before {α : Type} (value : α) :
    StatePrefixPreserves (fun h _ _=>Before h) Safe (pure value : WGPrefix Receipt α) :=
  StatePrefixEnsures.pure value (fun _ _ _ pre=>pre.safe) (fun _ _ _ pre=>pre)

theorem final_before {α : Type} (z : Ambient) (value : α) :
    StatePrefixEnsures (fun h _ _=>Before h) Safe (pure value : WGPrefix Receipt α)
      (fun _ h w _=>At h (Campaign2.snapshot w z).wg) :=
  StatePrefixEnsures.pure value (fun _ _ _ pre=>pre.safe) (fun _ _ _ pre=>pre.at _)

theorem record_before (attrs : DeviceAttrs) (kind : Kind)
    (notKey : kind≠.keyStage) (notPeer : ∀p,kind≠.peer p) :
    StatePrefixPreserves (fun h _ _=>Before h) Safe (record attrs kind) := by
  apply record_state_rule attrs kind (fun _ _ _ pre=>pre.safe)
  intro h g a result v b pre run
  have next:=pre.silent_append (receipt kind ⟨result,g,v,a,b⟩) notKey notPeer
  exact ⟨next.safe,next⟩

theorem key_at (attrs : DeviceAttrs) (z : Ambient) :
    StatePrefixEnsures (fun h _ _=>Before h) Safe (record attrs .keyStage)
      (fun _ h w _=>At h (Campaign2.snapshot w z).wg) := by
  apply record_state_rule attrs .keyStage (fun _ _ _ pre=>pre.safe)
  intro h g a result v b pre run
  have next:=pre.key_append (receipt .keyStage ⟨result,g,v,a,b⟩) rfl
  exact ⟨next.safe,next⟩

theorem keyed_at (attrs : DeviceAttrs) (z : Ambient) :
    StatePrefixEnsures (fun h _ _=>Before h) Safe (keyed attrs)
      (fun _ h w _=>At h (Campaign2.snapshot w z).wg) :=
  StatePrefixEnsures.bind (key_at attrs z) (fun _=>peers_at attrs z)


theorem fwmark_before (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h _ _=>Before h) Safe (fwmarkObserved attrs) := by
  intro g a h pre
  obtain ⟨added,eq,path,_⟩:=fwmarkObserved_conforms attrs g a h
  have kept : Before (runWGPrefix (fwmarkObserved attrs) g a h).2 := by
    rw [eq]
    exact pre.append (clear_before path)
  refine ⟨added,eq,kept.safe,?_⟩
  simp only [runWGPrefix,runStatePrefix] at kept ⊢
  cases run : (runPrefix ((fwmarkObserved attrs).run g) a h).1 with
  | error stop=>trivial
  | ok out=>exact kept

theorem afterPort_at (attrs : DeviceAttrs) (flags : UInt32) (z : Ambient) :
    StatePrefixEnsures (fun h _ _=>Before h) Safe (afterPort attrs flags)
      (fun _ h w _=>At h (Campaign2.snapshot w z).wg) := by
  unfold afterPort
  apply StatePrefixEnsures.bind (mark_before _ _)
  intro _
  split
  · apply StatePrefixEnsures.bind (record_before attrs .replacement
      (by intro h;cases h) (by intro p h;cases h))
    intro _
    exact keyed_at attrs z
  · exact keyed_at attrs z

theorem afterFwmark_at (attrs : DeviceAttrs) (flags : UInt32) (z : Ambient) :
    StatePrefixEnsures (fun h _ _=>Before h) Safe (afterFwmark attrs flags)
      (fun _ h w _=>At h (Campaign2.snapshot w z).wg) := by
  unfold afterFwmark
  apply StatePrefixEnsures.bind (mark_before _ _)
  intro _
  split
  · apply StatePrefixEnsures.bind (record_before attrs (.port _)
      (by intro h;cases h) (by intro p h;cases h))
    intro ret
    apply StatePrefixEnsures.bind (mark_before _ _)
    intro _
    split
    · unfold zero
      exact StatePrefixEnsures.bind (mark_before _ _) (fun _=>final_before z ret)
    · exact afterPort_at attrs flags z
  · exact afterPort_at attrs flags z

theorem update_at (attrs : DeviceAttrs) (flags : UInt32) (z : Ambient) :
    StatePrefixEnsures (fun h _ _=>Before h) Safe (update attrs flags)
      (fun _ h w _=>At h (Campaign2.snapshot w z).wg) := by
  rw [update_fwmark_factor]
  exact StatePrefixEnsures.bind (fwmark_before attrs) (fun _=>afterFwmark_at attrs flags z)

theorem observe_at (attrs : DeviceAttrs) (z : Ambient) :
    StatePrefixEnsures (fun h _ _=>Before h) Safe (observe attrs)
      (fun _ h w _=>At h (Campaign2.snapshot w z).wg) := by
  apply observe_entry_rule attrs
  · exact fun ret=>final_before z ret
  · exact fun site value=>mark_before site value
  · exact lift_before _
  · exact lift_before _
  · exact lift_before _
  · exact fun _ _ _ _=>lift_before _
  · exact StatePrefixEnsures.bind
      (record_before attrs (.updateEntry _) (by intro h;cases h) (by intro p h;cases h))
      (fun _=>update_at attrs _ z)

theorem inspection_facts (attrs : DeviceAttrs) (g : WGWorld) (a : Ambient) :
    Facts (inspection attrs g a) := by
  obtain ⟨_,_,safe,post⟩:=observe_at attrs a g a [] before_nil
  refine ⟨safe,?_⟩
  unfold inspection
  simp only [runWGPrefix,runStatePrefix] at post ⊢
  cases run : (runPrefix ((observe attrs).run g) a []).1 with
  | error stop=>trivial
  | ok out=>
    obtain ⟨⟨ret,v⟩,b⟩:=out
    have same : (Campaign2.snapshot v a).wg=(Campaign2.snapshot v b).wg := rfl
    simpa only [run,Campaign2.observeResult,Except.map,same] using post

theorem matches_facts (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (matched : Matches attrs initial result) : Facts result := by
  obtain ⟨g,a,_,rfl⟩:=matched
  exact inspection_facts attrs g a

end Leanux.Proofs.WG.Config.RequestOrder.WgLinks
