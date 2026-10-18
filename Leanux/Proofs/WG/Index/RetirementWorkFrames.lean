import Leanux.Proofs.WG.Config.QuietTimers
import Leanux.Proofs.WG.Index.RetirementWorkModel
import Leanux.Proofs.WG.Index.RetirementDischargeClaims
import Leanux.Proofs.WG.Index.RetirementClearWorkerClaims
import Leanux.Proofs.WG.Index.HashSlotClearWorkerClaims
import Leanux.Proofs.WG.Index.SelectedDrainSource
import Leanux.Proofs.WG.Noise.DriverTagRemovalSource
import Leanux.Proofs.WG.Origins.ConfiguredRemoval

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing Leanux.Proofs.Logged
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

/-- Physical timer deletion changes no hashed slot, owner metadata or stamped
retirement identity; it need not return on an absent peer. -/
theorem delTimer_retirementWork (original : DurableHolders) (cs : Ledger)
    (loans retired : Reservations) (pid : PeerId) (timer : PeerTimer) :
    Preserves (RetirementWork original cs loans retired) (delTimer pid timer) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  have account := (hoare_iff_run_ambient _ _ _).mp
    (DurableHolders.delTimer_preserves pid timer) w a () v b hi.account run
  have configured := (hoare_iff_run_ambient _ _ _).mp
    (ConfiguredRemoval.frame (ConfiguredIdentity.delTimer_view pid timer))
      w a () v b hi.configured run
  have base := BaseCoherence.transport hi.base
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.delTimer_view pid timer)
      w a () v b run)
  cases device : w.dev with
  | none =>
    simp [delTimer,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [delTimer,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨value,final,after,normal,present⟩ :=
        Config.delTimer_returns pid timer d p resident w a device
      rw [run] at normal
      cases normal
      refine ⟨account,configured,base,?_,?_,?_⟩
      · intro actual found
        have same : actual = Config.withPeer d pid ((p.setTimer timer none).setWheel timer none) :=
          Option.some.inj (found.symm.trans present)
        subst actual
        exact hashSlotCoverage_peerWrite d pid p _ resident
          (by cases timer <;> rfl) (hi.covered d device)
      · intro actual found
        have same : actual = Config.withPeer d pid ((p.setTimer timer none).setWheel timer none) :=
          Option.some.inj (found.symm.trans present)
        subst actual
        exact peerWrite_owner_coherent d pid p _ resident
          (by cases timer <;> rfl) (by cases timer <;> rfl) (hi.coherent d device)
      · intro actual found
        have same : actual = Config.withPeer d pid ((p.setTimer timer none).setWheel timer none) :=
          Option.some.inj (found.symm.trans present)
        subst actual
        exact peerWrite_deadHashedReserved retired d pid p _ resident
          (by cases timer <;> rfl) (by cases timer <;> rfl) (hi.reserved d device)

theorem decrement_retirementWork (original : DurableHolders) (cs : Ledger)
    (loans retired : Reservations) :
    Preserves (RetirementWork original cs loans retired)
      (modifyDev fun d => {d with numPeers := d.numPeers - 1}) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have account := (hoare_iff_run_ambient _ _ _).mp
    (pinned_const _private.Leanux.Proofs.WG.Queues.HolderRetirement.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.decrement_keeps)
      w a result v b hi.account run
  cases run
  refine ⟨account,?_,?_,?_,?_,?_⟩
  · intro s found
    apply hi.configured s
    have same : ConfiguredIdentity.view {w with dev := w.dev.map (fun d => {d with numPeers := d.numPeers - 1})} =
        ConfiguredIdentity.view w := by
      simp only [ConfiguredIdentity.view,Option.map_map,Function.comp_def]
      rfl
    exact same.symm.trans found
  · apply BaseCoherence.transport hi.base
    simp only [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,
      Option.map_map,Function.comp_def]
  · intro d found
    cases device : w.dev with
    | none => simp [device] at found
    | some old =>
      simp only [device,Option.map_some,Option.some.injEq] at found
      subst d
      exact hi.covered old device
  · intro d found
    cases device : w.dev with
    | none => simp [device] at found
    | some old =>
      simp only [device,Option.map_some,Option.some.injEq] at found
      subst d
      exact hi.coherent old device
  · intro d found
    cases device : w.dev with
    | none => simp [device] at found
    | some old =>
      simp only [device,Option.map_some,Option.some.injEq] at found
      subst d
      exact hi.reserved old device

end Leanux.Proofs.WG.Index
