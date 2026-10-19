import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedQueueStops

/-! The original create admission read and dead-peer guard precede queue
installation. This fixed prefix starts at that actual admission entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation HandshakeSecurity.StagedDisposal

def admissionInstallPrefix (pid : PeerId) (items : List SkbId) :
    PrefixM CausalJournal.Event (Option Bool) := do
  let peer ← Admission.actualOps.access (getPeerMixed pid)
  if ← Admission.actualOps.step (branch .createDataDead peer.isDead) then return none
  return some (← queueInstallPrefix pid items)

def admissionInstallTail (items : List SkbId) :
    Option Bool → PrefixM CausalJournal.Event Int
  | none => pure (-EINVAL)
  | some installed => do
      let ret ← queueInstallTail items installed
      if ← Admission.actualOps.step (branch .createDataEpipe (ret == -WG.EPIPE)) then
        TxSource.publish Admission.actualOps items .dead
      return ret

theorem admission_install_factor (pid : PeerId) (items : List SkbId) :
    Admission.actual pid items = (admissionInstallPrefix pid items >>= admissionInstallTail items) := by
  unfold Admission.actual Admission.front admissionInstallPrefix
  simp only [queue_install_factor,bind_assoc]
  congr 1
  funext peer
  congr 1
  funext dead
  cases dead <;> simp only [Bool.false_eq_true,↓reduceIte,pure_bind,bind_assoc,admissionInstallTail]

theorem admission_install_prefix_run
    (read : runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history = (.ok (peer,u),readHistory))
    (guarded : runPrefix (Admission.actualOps.step (branch .createDataDead peer.isDead)) u readHistory =
      (.ok (false,q),readHistory))
    (installed : runPrefix (queueInstallPrefix pid items) q readHistory = (.ok (true,v),last)) :
    runPrefix (admissionInstallPrefix pid items) w history = (.ok (some true,v),last) := by
  simp only [admissionInstallPrefix,runPrefix_bind,read,guarded,Bool.false_eq_true,↓reduceIte,installed,runPrefix_pure]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
