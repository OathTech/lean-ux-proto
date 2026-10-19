import Leanux.Proofs.WG.Config.RequestRefusalEffects
import Leanux.Proofs.WG.Config.RequestReceiptEffectBridge
import Leanux.Proofs.WG.Config.RequestRefusalFrames
import Leanux.Proofs.WG.Config.RequestOrderInspectionSource

/-! The existing device-request observer links a refused port receipt to the normal request endpoint. No second observer is executed. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration
open Internal

theorem Conforms.refusalSilent {α : Type} {a : WGPrefix Receipt α} {L : Language α}
    (law : Conforms a L) (silent : RefusalSilent L) :
    StatePrefixPreserves (fun h _ _ => NoRefusal h) (fun _ => True) a := by
  intro w ambient h point
  obtain ⟨added,eq,path,_⟩ := law w ambient h
  have all : NoRefusal (runWGPrefix a w ambient h).2 := by
    rw [eq]
    exact point.append (silent added path)
  refine ⟨added,eq,trivial,?_⟩
  simp only [runWGPrefix,runStatePrefix] at all ⊢
  cases run : (runPrefix (a.run w) ambient h).1 with
  | error stop => trivial
  | ok out =>
    rcases out with ⟨⟨ret,v⟩,after⟩
    exact all

private theorem noRefusal_lift {α : Type} (a : WG.M α) :
    StatePrefixPreserves (fun h _ _ => NoRefusal h) (fun _ => True) (liftWGPrefix a) :=
  StatePrefixEnsures.lift a (fun _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ point _ => point)

private theorem noRefusal_pure {α : Type} (value : α) :
    StatePrefixPreserves (fun h _ _ => NoRefusal h) (fun _ => True) (pure value : WGPrefix Receipt α) :=
  StatePrefixEnsures.pure value (fun _ _ _ _ => trivial) (fun _ _ _ point => point)

private theorem mark_predicate (P : List Receipt → WGWorld → Prop)
    (site : Decision) (value : Bool) :
    StatePrefixPreserves (fun h w _ => P h w) (fun _ => True) (mark site value) :=
  (frame_predicate P (branch site value) (Internal.ambient_frame _)).bind
    (fun _ => StatePrefixEnsures.pure () (fun _ _ _ _ => trivial) (fun _ _ _ point => point))

private theorem noRefusal_mark (site : Decision) (value : Bool) :
    StatePrefixPreserves (fun h _ _ => NoRefusal h) (fun _ => True) (mark site value) :=
  mark_predicate (fun h _ => NoRefusal h) site value

private theorem record_port_endpoint (attrs : DeviceAttrs) (port : Nat) (a : Ambient) :
    StatePrefixEnsures (fun h _ _ => NoRefusal h) (fun _ => True)
      (record attrs (.port port)) (fun ret h w _ => AfterPortRecord a port ret h w) := by
  have captured : StatePrefixEnsures (fun h _ _ => NoRefusal h) (fun _ => True)
      (Logged.captureWGRun (action attrs (.port port)))
      (fun native h w ambient => NoRefusal h ∧ native.after = w ∧
        native.ambientAfter = ambient) :=
    StatePrefixEnsures.captureWGRun _ (fun _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ point _ => ⟨point,rfl,rfl⟩)
  unfold record receiptWGObserved
  apply StatePrefixEnsures.bind captured
  intro native
  apply StatePrefixEnsures.bind
    (StatePrefixEnsures.emit (Q := fun _ h w _ => AfterPortRecord a port native.value h w)
      (receipt (.port port) native) (fun _ _ _ _ => trivial)
      (fun h w ambient point => (show AfterPortRecord a port native.value
        (h ++ [receipt (.port port) native]) w from
          ⟨h,receipt (.port port) native,rfl,point.1,rfl,rfl,by
            simp only [receipt,point.2.1,Campaign2.snapshot]⟩)))
  intro _
  exact StatePrefixEnsures.pure native.value (fun _ _ _ _ => trivial)
    (fun _ _ _ point => point)

private theorem zero_refusal (attrs : DeviceAttrs) (ret : Int) (a : Ambient) :
    StatePrefixEnsures (fun h w _ => RefusalFinal ret h (Campaign2.snapshot w a).wg)
      (fun _ => True) (zero attrs ret)
      (fun value h w _ => RefusalFinal value h (Campaign2.snapshot w a).wg) :=
  (mark_predicate (fun h w => RefusalFinal ret h (Campaign2.snapshot w a).wg)
    .setDevZeroKey attrs.privateKey.isSome).bind
      (fun _ => StatePrefixEnsures.pure ret (fun _ _ _ _ => trivial)
        (fun _ _ _ point => point))

private theorem afterPort_refusal (attrs : DeviceAttrs) (flags : UInt32) (a : Ambient) :
    StatePrefixEnsures (fun h _ _ => NoRefusal h) (fun _ => True)
      (afterPort attrs flags)
      (fun ret h w _ => RefusalFinal ret h (Campaign2.snapshot w a).wg) :=
  ((afterPort_conforms attrs flags).refusalSilent (afterPort_refusalSilent attrs flags)).consequence
    (fun _ _ _ point => point) (fun ret _ _ _ point => point.final ret _)

theorem afterFwmark_refusal (attrs : DeviceAttrs) (flags : UInt32) (a : Ambient) :
    StatePrefixEnsures (fun h _ _ => NoRefusal h) (fun _ => True)
      (afterFwmark attrs flags)
      (fun ret h w _ => RefusalFinal ret h (Campaign2.snapshot w a).wg) := by
  unfold afterFwmark
  apply StatePrefixEnsures.bind (noRefusal_mark _ _)
  intro _
  split
  · apply StatePrefixEnsures.bind (record_port_endpoint attrs _ a)
    intro ret
    apply StatePrefixEnsures.bind (mark_predicate (AfterPortRecord a _ ret) _ _)
    intro _
    split
    · apply (zero_refusal attrs ret a).consequence
      · intro h w ambient point
        exact point.final
      · exact fun _ _ _ _ point => point
    · apply (afterPort_refusal attrs flags a).consequence
      · intro h w ambient point
        exact point.zero (by
          by_cases eq : ret = 0
          · exact eq
          · exact False.elim (‹¬ ret != 0› (by simpa only [bne_iff_ne] using eq)))
      · exact fun _ _ _ _ point => point
  · exact afterPort_refusal attrs flags a

private theorem noRefusal_record (attrs : DeviceAttrs) (kind : Kind)
    (silent : ∀ port, kind ≠ .port port) :
    StatePrefixPreserves (fun h _ _ => NoRefusal h) (fun _ => True) (record attrs kind) :=
  (record_conforms attrs kind).refusalSilent (event_refusalSilent kind silent)

private theorem noRefusal_clearLoop (attrs : DeviceAttrs) (pids : List PeerId) :
    StatePrefixPreserves (fun h _ _ => NoRefusal h) (fun _ => True)
      (forIn pids () fun pid _ => do
        mark .setDevFwmarkPeerIter true
        let _ ← record attrs (.clearSource pid)
        pure (ForInStep.yield ())) := by
  apply StatePrefixEnsures.forInInvariant pids () _ (fun _ h _ _ => NoRefusal h)
    (fun _ => True) (fun _ _ _ _ _ => trivial)
  intro pid _
  apply StatePrefixEnsures.bind (noRefusal_mark _ _)
  intro _
  apply StatePrefixEnsures.bind
    (noRefusal_record attrs (.clearSource pid) (by intro port eq; cases eq))
  intro _
  exact noRefusal_pure _

theorem update_refusal (attrs : DeviceAttrs) (flags : UInt32) (a : Ambient) :
    StatePrefixEnsures (fun h _ _ => NoRefusal h) (fun _ => True)
      (update attrs flags)
      (fun ret h w _ => RefusalFinal ret h (Campaign2.snapshot w a).wg) := by
  rw [update_factor]
  apply StatePrefixEnsures.bind
  · apply StatePrefixEnsures.bind (noRefusal_mark _ _)
    intro _
    split
    · apply StatePrefixEnsures.bind (noRefusal_lift _)
      intro _
      apply StatePrefixEnsures.bind (noRefusal_lift _)
      intro d
      apply StatePrefixEnsures.bind (noRefusal_clearLoop attrs d.peerList)
      intro _
      exact noRefusal_mark _ _
    · exact noRefusal_pure ()
  · intro _
    exact afterFwmark_refusal attrs flags a

private theorem pure_refusal (ret : Int) (a : Ambient) :
    StatePrefixEnsures (fun h _ _ => NoRefusal h) (fun _ => True)
      (pure ret : WGPrefix Receipt Int)
      (fun value h w _ => RefusalFinal value h (Campaign2.snapshot w a).wg) :=
  StatePrefixEnsures.pure ret (fun _ _ _ _ => trivial)
    (fun _ _ _ point => point.final ret _)

theorem observe_refusal (attrs : DeviceAttrs) (a : Ambient) :
    StatePrefixEnsures (fun h _ _ => NoRefusal h) (fun _ => True)
      (observe attrs)
      (fun ret h w _ => RefusalFinal ret h (Campaign2.snapshot w a).wg) := by
  have next : StatePrefixEnsures (fun h _ _ => NoRefusal h) (fun _ => True)
      (accepted attrs (attrs.flags.getD 0))
      (fun ret h w _ => RefusalFinal ret h (Campaign2.snapshot w a).wg) :=
    StatePrefixEnsures.bind
      (noRefusal_record attrs (.updateEntry (attrs.flags.getD 0))
        (by intro port eq; cases eq))
      (fun _ => update_refusal attrs (attrs.flags.getD 0) a)
  unfold observe setDeviceWith
  simp only [branch_factor,bind_assoc,pure_bind]
  cases flags : attrs.flags <;>
    simp only [flags,Option.isSome_none,Option.isSome_some,Option.getD_none,Option.getD_some,
      Bool.false_eq_true,ite_false,ite_true] at next ⊢
  all_goals
    repeat' first
      | (maintenance_head accepted; exact next)
      | (maintenance_head Pure.pure; exact pure_refusal _ a)
      | (maintenance_head mark; exact noRefusal_mark _ _)
      | (maintenance_head liftWGPrefix; exact noRefusal_lift _)
      | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind)
      | (maintenance_intro; try dsimp only)
      | split

theorem inspection_refusal (attrs : DeviceAttrs) (w : WGWorld) (ambient : Ambient) :
    RefusalFacts (inspection attrs w ambient) := by
  obtain ⟨_,_,_,post⟩ := observe_refusal attrs ambient w ambient []
    (by simp [NoRefusal])
  cases run : (runWGPrefix (observe attrs) w ambient []).1 with
  | error stop =>
    simp only [RefusalFacts,inspection,Campaign2.observeResult,run,Except.map]
  | ok out =>
    rcases out with ⟨⟨ret,v⟩,after⟩
    simp only [runWGPrefix,runStatePrefix] at run post
    simpa only [RefusalFacts,inspection,Campaign2.observeResult,runWGPrefix,
      runStatePrefix,run,Except.map,Campaign2.snapshot] using post

theorem matches_refusal (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (matched : Matches attrs entry result) : RefusalFacts result := by
  obtain ⟨w,ambient,_,rfl⟩ := matched
  exact inspection_refusal attrs w ambient

end Leanux.Proofs.WG.Config.RequestOrder
