import Leanux.Proofs.WG.Queues.RunnerTailSelection

/-! Initialization retains the exact prefill/boot choice and carries the
concrete syscall query through the unchanged runner. The helper certificates
leave their continuation explicit; no initialized result is assumed. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.RunnerSelection
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open AdmissionSelection RunnerSelectionData

def reindex {action other : PrefixOuter RxHistory.Event α} (same : action=other)
    (rule : ConservationOuter.Rule action) (selected : Selection rule) :
    Selection (ConservationOuter.reindex same rule) where
  query := selected.query
  fates := selected.fates
  effects := selected.effects

def prefill (count : Nat) (w : World) (next : World → PrefixOuter RxHistory.Event α)
    (checked : ∀v,wgStoreView v.wg=wgStoreView w.wg → ConservationCertified.Certified (next v) P Q)
    (selected : ∀v same,Selection (checked v same).rule) :
    Selection (ConservationRunner.prefillCertified count w next checked).rule where
  query operation inner := fun {cs h out k final} _ c =>
    if count > 0 then
      match Env.seccompPrefill count w.seccomp w.tasks with
      | .ok result => ∃ same, ∃ front : (checked { w with seccomp := result.1, tasks := result.2 } same).rule.relation cs h out k final,
          (selected _ same).query operation inner front c
      | .error _ => False
    else ∃ front : (checked w rfl).rule.relation cs h out k final,
      (selected w rfl).query operation inner front c
  fates operation inner := by
    intro cs h out k final source c choice
    split at choice
    · split at choice
      · obtain ⟨same,front,chosen⟩ := choice
        exact (selected _ same).fates operation inner front chosen
      · exact False.elim choice
    · obtain ⟨front,chosen⟩ := choice
      exact (selected w rfl).fates operation inner front chosen
  effects := by
    intro cs h out k final source
    unfold ConservationRunner.prefillCertified at source
    split at source
    · split at source
      · exact (selected _ _).effects source
      · exact False.elim source
    · exact (selected w rfl).effects source

def boot (net foreign : Bool) (w : World) (next : World → PrefixOuter RxHistory.Event α)
    (checked : ∀v,wgStoreView v.wg=wgStoreView w.wg → ConservationCertified.Certified (next v) P Q)
    (selected : ∀v same,Selection (checked v same).rule) :
    Selection (ConservationRunner.bootCertified net foreign w next checked).rule where
  query operation inner := fun {cs h out k final} _ c =>
    if net then
      match (do Net.Fib.bootTables; if foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit).run w with
      | .ok result => ∃ same, ∃ front : (checked { result.2 with ambient := { result.2.ambient with steps := #[], envCalls := [] } } same).rule.relation cs h out k final,
          (selected _ same).query operation inner front c
      | .error _ => False
    else ∃ front : (checked w rfl).rule.relation cs h out k final,
      (selected w rfl).query operation inner front c
  fates operation inner := by
    intro cs h out k final source c choice
    split at choice
    · split at choice
      · obtain ⟨same,front,chosen⟩ := choice
        exact (selected _ same).fates operation inner front chosen
      · exact False.elim choice
    · obtain ⟨front,chosen⟩ := choice
      exact (selected w rfl).fates operation inner front chosen
  effects := by
    intro cs h out k final source
    unfold ConservationRunner.bootCertified at source
    split at source
    · split at source
      · exact (selected _ _).effects source
      · exact False.elim source
    · exact (selected w rfl).effects source

def initialized (call : Syscall→RxHistory.Obs Int)
    (rules : ∀c,ConservationSource.Rule (call c))
    (established : ∀c,HolderTrafficDispatch.Established (rules c) [])
    (queries : ∀c,Nat→Query (rules c))
    (chosen : ∀c inner,Fates (queries c inner))
    (effects : ∀c,ConservationEffects.Conserves (rules c))
    (trace : Trace) (placeholders : Bool) :
    Selection (ConservationRunner.initialized call rules established trace placeholders).rule := by
  unfold ConservationRunner.initialized
  refine RunnerSelection.reindex (ConservationRunner.initialized_factor call trace placeholders).symm _ ?_
  apply prefill
  intro w before
  apply boot
  intro v after
  exact tail call rules established queries chosen effects trace v

/-- Selection on the actual initialized account. The operation number is
the actual runAt index; the inner number is its ordered traffic position. -/
def account (trace : Trace) (placeholders : Bool) :
    Selection (RunnerAccount.rule trace placeholders) :=
  initialized RxHistory.syscall ConservationSyscall.rule ConservationSyscall.established
    SyscallSelection.syscall SyscallSelection.syscall_fates SyscallEffects.syscall trace placeholders

end Leanux.Proofs.WG.Queues.RxCredits.RunnerSelection
