import Leanux.Proofs.WG.RetirementSecurity.KeySlotSourceFrames
import Leanux.Proofs.WG.Origins.CurrentTraffic

/-! The original session and responder-confirmation paths cannot introduce
published slots for a dead peer. The session's successful native tail supplies
its live check; confirmation obtains liveness from its already-published next
slot. Other resident peers are retained by the source perimeter theorem. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem configured_alive (same : ConfiguredIdentity.view v=ConfiguredIdentity.view w)
    (live : ∃s p,ConfiguredIdentity.view w=some s ∧ s.peers pid=some p ∧ p.dead=false)
    (found : peerAt v pid=some q) : q.isDead=false := by
  obtain ⟨d,device,resident⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨s,p,state,stored,alive⟩ := live
  have view : some (ConfiguredIdentity.state d)=some s := by
    simpa only [ConfiguredIdentity.view,device,Option.map_some] using same.trans state
  have stateEq := Option.some.inj view
  subst s
  have cellEq : ConfiguredIdentity.cell q=p := by
    simpa only [ConfiguredIdentity.state,resident,Option.map_some,Option.some.injEq] using stored
  exact (congrArg ConfiguredIdentity.Cell.dead cellEq).trans alive

theorem except_selected (before : InvExcept pending w)
    (perimeter : holderPerimeter pid v=holderPerimeter pid w)
    (selected : ∀p,peerAt v pid=some p → pid∉pending → HasKeySlot p → p.isDead=false) :
    InvExcept pending v := by
  intro other p found outside slots
  by_cases same : other=pid
  · subst other; exact selected p found outside slots
  · have equal := congrFun (congrArg Prod.fst perimeter) other
    have point : peerAt v other=peerAt w other := by
      simpa only [holderPerimeter,same,ite_false,peerAt,peersAt,Option.bind_map,Function.comp_def] using equal
    exact before other p (point.symm.trans found) outside slots

theorem session (pid : PeerId) : Preserves (InvExcept pending) (beginSession pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have source := run
  rw [SessionOrigin.factor,MaterialOrigin.bind_ok_ambient] at source
  obtain ⟨context,middle,c,front,tail⟩ := source
  cases context with
  | none =>
    cases tail
    exact (Origins.front_none pid w v a b front) ▸ before
  | some ctx =>
    have live := ConfiguredSession.tail_live pid ctx.slot middle v result c b tail
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (ConfiguredSession.tail_view pid ctx.slot) middle c result v b tail
    apply except_selected before ((ProjectedAction.iff_run_ambient _ _ _).mp
      (session_perimeter pid) w a result v b run)
    intro p found _ _
    obtain ⟨s,q,state,stored,alive,_⟩ := live
    exact configured_alive same ⟨s,q,state,stored,alive⟩ found

theorem confirmation (pid : PeerId) (key : KeypairId) :
    Preserves (InvExcept pending) (receivedWithKeypair pid key) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have source := run
  unfold receivedWithKeypair at source
  rw [MaterialOrigin.bind_ok_ambient] at source
  obtain ⟨p,read,c,getter,tail⟩ := source
  obtain ⟨same,time,d,device,stored⟩ := getPeer_normal pid w read p a c getter
  subst read
  subst c
  by_cases next : p.keypairNext=some key
  · apply except_selected before ((ProjectedAction.iff_run_ambient _ _ _).mp
      (confirmation_perimeter pid key) w a result v b run)
    intro q found outside _
    have alive := before pid p (by simp [peerAt,device,stored]) outside
      (Or.inl (by simp [next]))
    apply configured_alive ((ProjectedAction.iff_run_ambient _ _ _).mp
      ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.receivedWithKeypair_view) pid key)
      w a result v b run) _ found
    exact ⟨ConfiguredIdentity.state d,ConfiguredIdentity.cell p,
      by simp [ConfiguredIdentity.view,device],by simp [ConfiguredIdentity.state,stored],alive⟩
  · simp [next,branch,AmbientM.branch] at tail
    exact tail.1.2 ▸ before

theorem clear (pid : PeerId) : Preserves (InvExcept pending) (keypairsClear pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have cleared := (hoare_iff_run_ambient _ _ _).mp (clear_slots pid) w a result v b True.intro run
  apply except_selected before ((ProjectedAction.iff_run_ambient _ _ _).mp
    (ClearedSlots.clear_perimeter pid) w a result v b run)
  intro p found _ slots
  have empty := cleared p found
  simp only [HasKeySlot,empty.1,empty.2.1,empty.2.2,ne_eq,not_true_eq_false,or_self] at slots

theorem discharge (before : InvExcept (pid::pending) w) (cleared : SlotsCleared pid w) :
    InvExcept pending w := by
  intro other p found outside slots
  by_cases same : other=pid
  · subst other
    have empty := cleared p found
    simp only [HasKeySlot,empty.1,empty.2.1,empty.2.2,ne_eq,not_true_eq_false,or_self] at slots
  · exact before other p found (by simp [List.mem_cons,same,outside]) slots

/-- The actual clear discharges the selected make-dead exception; no claim is
made that the intervening unpublished peer was live or that its key allocation
was destroyed while other physical references remain. -/
theorem clear_discharge (pid : PeerId) : Hoare (keypairsClear pid)
    (InvExcept (pid::pending)) (fun _=>InvExcept pending) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact discharge ((hoare_iff_run_ambient _ _ _).mp (clear pid) w a result v b before run)
    ((hoare_iff_run_ambient _ _ _).mp (clear_slots pid) w a result v b True.intro run)

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
