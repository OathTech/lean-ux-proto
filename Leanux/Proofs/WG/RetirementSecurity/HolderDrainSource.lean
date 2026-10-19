import Leanux.Proofs.WG.RetirementSecurity.SlotAnchorWorkers
import Leanux.Proofs.WG.Queues.HolderDrains

/-! A source rule for the actual bounded handshake workqueue drain. The
callback premises apply only to an item selected from the saved native queue,
including recorded-unit resolution and legacy head selection. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderDrain
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem ambient_cut (action : AmbientM α) (w v : WGWorld) (a b : Ambient)
    (run : (((monadLift action : WG.M α)).run w).run a=.ok ((x,v),b)) :
    v=w ∧ action.run a=.ok (x,b) := by
  change (((StateT.lift action : WG.M α).run w).run a)=.ok ((x,v),b) at run
  rw [stateLiftAmbient_run] at run
  cases h : action.run a with
  | error e => simp [h,Except.map] at run
  | ok out =>
    rcases out with ⟨y,c⟩
    simp only [h,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact ⟨rfl,rfl⟩

/-- Every normal iteration pays only an occurrence selected from its actual
saved queue. Exhaustion and missing/malformed section records still stop. -/
theorem drain_rule (upTo : Option PeerId) (P : WGWorld → Prop)
    (send : ∀ (w v : WGWorld) (d : Device) (pid : PeerId) (a b : Ambient),
      P w → w.dev = some d → pid ∈ d.sendWorkQueue →
      ((runFlushedSendWork pid).run w).run a = .ok (((),v),b) → P v)
    (clear : ∀ (w v : WGWorld) (d : Device) (pid : PeerId) (a b : Ambient),
      P w → w.dev = some d → pid ∈ d.clearWorkQueue →
      ((runFlushedClearWork pid).run w).run a = .ok (((),v),b) → P v) :
    Preserves P (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply preserves_bind
  · apply list_view_spec id P
    intro i acc
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a step v b hi hr
    dsimp only at hr
    rw [MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨d,read,ar,getter,rest⟩ := hr
    obtain ⟨readEq,ambientEq,hd⟩ := DecryptCarrier.getDev_current a ar getter
    subst read
    subst ar
    split at rest
    · cases rest; exact hi
    · rw [MaterialOrigin.bind_ok_ambient] at rest
      obtain ⟨unit,peeked,ap,peek,rest⟩ := rest
      obtain ⟨same,_⟩ := ambient_cut (AmbientM.peekUnit .sendWorker) w peeked a ap peek
      subst peeked
      cases unit with
      | some u =>
        simp only [MaterialOrigin.bind_ok_ambient] at rest
        obtain ⟨pid,picked,ac,resolve,done,paid,ad,worker,finish⟩ := rest
        obtain ⟨same,resolver⟩ := ambient_cut (AmbientM.resolveUnit .sendWorker u d.sendWorkQueue) w picked ap ac resolve
        subst picked
        cases done
        have kept := send w paid d pid ac ad hi hd (ClearWork.resolveUnit_member _ _ _ _ _ _ resolver).1 worker
        cases finish
        exact kept
      | none =>
        simp only [MaterialOrigin.bind_ok_ambient] at rest
        obtain ⟨unit,peeked,ac,peek,rest⟩ := rest
        obtain ⟨same,_⟩ := ambient_cut (AmbientM.peekUnit .clearPeerWorker) w peeked ap ac peek
        subst peeked
        cases unit with
        | some u =>
          simp only [MaterialOrigin.bind_ok_ambient] at rest
          obtain ⟨pid,picked,ar,resolve,done,paid,ad,worker,finish⟩ := rest
          obtain ⟨same,resolver⟩ := ambient_cut (AmbientM.resolveUnit .clearPeerWorker u d.clearWorkQueue) w picked ac ar resolve
          subst picked
          cases done
          have kept := clear w paid d pid ar ad hi hd (ClearWork.resolveUnit_member _ _ _ _ _ _ resolver).1 worker
          split at finish <;> cases finish <;> exact kept
        | none =>
          simp only [MaterialOrigin.bind_ok_ambient] at rest
          obtain ⟨current,read,ar,getter,rest⟩ := rest
          obtain ⟨same,_⟩ := ambient_cut (get : AmbientM Ambient) w read ac ar getter
          subst read
          split at rest
          · cases rest
          · cases hs : d.sendWorkQueue.head? with
            | some pid =>
              simp only [hs,MaterialOrigin.bind_ok_ambient] at rest
              obtain ⟨done,paid,ad,worker,finish⟩ := rest
              cases done
              have kept := send w paid d pid ar ad hi hd (List.mem_of_head? hs) worker
              cases finish
              exact kept
            | none =>
              cases hc : d.clearWorkQueue.head? with
              | none => simp only [hs,hc] at rest; cases rest; exact hi
              | some pid =>
                simp only [hs,hc,MaterialOrigin.bind_ok_ambient] at rest
                obtain ⟨done,paid,ad,worker,finish⟩ := rest
                cases done
                have kept := clear w paid d pid ar ad hi hd (List.mem_of_head? hc) worker
                split at finish <;> cases finish <;> exact kept
  · intro result
    rcases result with ⟨result,⟨⟩⟩
    cases result with
    | none => exact hoare_liftAmbient (AmbientM.invariant _) _
    | some result => exact preserves_pure result


end Leanux.Proofs.WG.RetirementSecurity.HolderDrain
