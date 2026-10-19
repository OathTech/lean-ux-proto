import Leanux.Proofs.WG.TimerDiscipline.SessionWheelEffects
import Leanux.Proofs.WG.TimerDiscipline.SessionWheelFrames
import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalClaims
import Leanux.Proofs.WG.TimerDiscipline.HookJournalClaims
import Leanux.Proofs.WG.TimerDiscipline.ResponseSessionEffects

/-! Reuse the exact original session effect to derive live hook-entry residency, then attach the normal wheel effect to the same valid session/hook pair. No new observer or operational traversal. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG

theorem SessionReceipt.Valid.live {r : SessionReceipt} (valid : r.Valid) (begun : r.begun=true) :
    ∃ d p, r.after.wg.device=some d ∧ d.peers[r.pid]?=some p ∧ p.isDead=false := by
  obtain ⟨d,p,final,_,_,present,effect⟩:=valid.effect
  rw [begun] at effect
  obtain ⟨q,resident,alive⟩:=sessionEffect_alive r.pid d p _ _ final effect
  exact ⟨final,q,present,resident,alive⟩

theorem session_wheel {s : SessionReceipt} {r : HookJournal.Receipt}
    (sessionValid : s.Valid) (hookValid : r.Valid) (link : SessionDerivedLink s r) :
    SessionWheelFacts s r := by
  obtain ⟨begun,kind,pid,cut,serial⟩:=link
  obtain ⟨d,p,device,resident,alive⟩:=sessionValid.live begun
  have before : r.before.wg.device=some d := by rw [cut];exact device
  have selected : d.peers[r.pid]?=some p := by rw [pid];exact resident
  refine ⟨⟨begun,kind,pid,cut,serial⟩,d,p,before,selected,alive,?_⟩
  cases normal : r.outcome with
  | error _ => trivial
  | ok out =>
    obtain ⟨value,after⟩:=out
    cases value
    have counters:=hookValid.sessionDerived_counters kind d p before selected normal
    have effect:=hookValid.sessionDerived kind d p before selected normal
    refine ⟨counters.1.trans serial,?_⟩
    simp only [alive,Bool.not_false,Bool.and_true] at effect
    split
    · rename_i running
      rw [ite_eq_left running] at effect
      exact ⟨effect,arm_zero_delta r.before d r.pid p before selected after.wg effect,
        arm_zero_other r.before r.pid p after.wg effect⟩
    · rename_i stopped
      simpa only [ite_eq_right stopped] using effect

theorem history_wheel {h : List Event} (valid : ValidHistory h) (paired : Paired h)
    (r : HookJournal.Receipt) (kind : r.hook=.sessionDerived) (member : Event.hook r∈h) :
    ∃ before s after,h=before++[.session s,.hook r]++after ∧ SessionWheelFacts s r := by
  obtain ⟨before,s,after,same,link⟩:=paired.hook_origin r kind member
  have sv : s.Valid := valid (.session s) (by rw [same];simp)
  have rv : r.Valid := valid (.hook r) member
  exact ⟨before,s,after,same,session_wheel sv rv link⟩
theorem inspect_wheel {α : Type} (observer : Obs α)
    (valid : Leanux.Proofs.Logged.StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory observer)
    (paired : Leanux.Proofs.Logged.StatePrefixPreserves (fun h _ _=>Paired h) Paired observer) :
    Campaign2.Returns (inspect observer) (fun _=>True) (fun result _=>WheelHistoryFacts result.2) := by
  intro g a _
  obtain ⟨result,final,after,run,hv,hp,_⟩:=inspect_facts observer valid paired g a True.intro
  exact ⟨result,final,after,run,fun r kind member=>history_wheel hv hp r kind member⟩

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
