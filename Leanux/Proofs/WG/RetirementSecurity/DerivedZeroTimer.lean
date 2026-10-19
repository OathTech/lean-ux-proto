import Leanux.Proofs.WG.RetirementSecurity.UnpublicationWorker
import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsReceipts

/-! Exact session-derived timer source cuts. A rejected guard need not arm
anything; a reached arm uses the zero-key timer and its native delay. -/
namespace Leanux.Proofs.WG.RetirementSecurity.DerivedZeroTimer
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects.TimerEffects

theorem source [Monad m] [LawfulMonad m] (o : Ops m) (pid : PeerId) :
    derivedWith o pid=(do
      let caller←o.step (callerJiffies .timerJiffiesSessionDerived)
      if ←o.step (modPeerTimerGuard pid) then
        o.arm pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS caller) := by
  simp only [derivedWith,modifyWith,Functor.discard,map_const,Function.comp_apply,
    Function.const,map_eq_pure_bind,bind_assoc]
  congr 1
  funext caller
  congr 1
  funext allowed
  cases allowed <;> simp

/-- The actual session callback either refuses its guard or completes the
native zero-key arm after the caller's own clock read. No future dispatch is
inferred from merely completing the callback. -/
theorem native (pid : PeerId) (a b : Ambient)
    (run : ((timersSessionDerived pid).run w).run a=.ok (((),v),b)) :
    ∃ caller u c,
      ((callerJiffies .timerJiffiesSessionDerived).run w).run a=.ok ((caller,u),c) ∧
      (((modPeerTimerGuard pid).run u).run c=.ok ((false,v),b) ∨
        ∃ t e, ((modPeerTimerGuard pid).run u).run c=.ok ((true,t),e) ∧
          ((armTimer pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS caller).run t).run e=.ok (((),v),b)) := by
  rw [derived_factor,source] at run
  simp only [AuthenticatedEffects.TimerEffects.native,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨caller,u,c,clock,allowed,t,e,guard,tail⟩ := run
  refine ⟨caller,u,c,clock,?_⟩
  cases allowed with
  | false=>
    simp at tail
    obtain ⟨rfl,rfl⟩ := tail
    exact .inl guard
  | true=>
    exact .inr ⟨t,e,guard,tail⟩

/-- Every new receipt in the generic session-derived observer is an actual
completed zero-key arm with the source's exact delay and causal token. This
also covers prefixes ending in a native Stop. -/
theorem receipts (recordArm : Arm Cause → E) (recordQueue : Queued Cause → E)
    (cause : Cause) (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List E) :
    ∃ suffix,
      (runWGPrefix (derivedWith (AuthenticatedEffects.TimerEffects.receipts recordArm recordQueue cause) pid) w a h).2=
        h++suffix ∧
      ∀ event∈suffix,∃ r : Arm Cause,event=recordArm r ∧ r.Valid ∧
        r.cause=cause ∧ r.peer=pid ∧ r.timer=.zeroKeyMaterial ∧ r.delay=ZERO_KEY_MATERIAL_TICKS := by
  rw [source]
  unfold AuthenticatedEffects.TimerEffects.receipts observed
  change ∃ suffix,(runStatePrefix _ w a h).2=h++suffix ∧ _
  simp only [runStatePrefix_bind,liftWGPrefix,runStatePrefix_lift]
  cases clock:((callerJiffies .timerJiffiesSessionDerived).run w).run a with
  | error stop=>exact ⟨[],by simp,by simp⟩
  | ok result=>
    rcases result with ⟨⟨caller,u⟩,c⟩
    simp only
    cases guard:((modPeerTimerGuard pid).run u).run c with
    | error stop=>exact ⟨[],by simp,by simp⟩
    | ok result=>
      rcases result with ⟨⟨allowed,t⟩,e⟩
      cases allowed with
      | false=>exact ⟨[],by simp,by simp⟩
      | true=>
        change ∃ suffix,(runWGPrefix (armReceipt recordArm cause pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS caller) t e h).2=h++suffix ∧ _
        rw [armReceipt,runWGPrefix_receiptWGObserved,runWGPrefix_lift]
        cases armed:((armTimer pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS caller).run t).run e with
        | error stop=>exact ⟨[],by simp,by simp⟩
        | ok result=>
          rcases result with ⟨⟨value,v⟩,b⟩
          cases value
          let r : Arm Cause:=⟨cause,pid,.zeroKeyMaterial,ZERO_KEY_MATERIAL_TICKS,caller,⟨(),t,v,e,b⟩⟩
          refine ⟨[recordArm r],rfl,?_⟩
          intro event member
          have same:event=recordArm r:=by simpa using member
          exact ⟨r,same,armed,rfl,rfl,rfl,rfl⟩

end Leanux.Proofs.WG.RetirementSecurity.DerivedZeroTimer
