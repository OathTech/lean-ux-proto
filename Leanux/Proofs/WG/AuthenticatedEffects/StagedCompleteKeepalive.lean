import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryKeepaliveSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryCompleteCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteLedgerFrames

/-! Keepalive preparation preserves complete terminal accounting on its exact
successor ledger. Only the actual successful empty-queue arm admits a birth;
a true return with an existing queue changes neither births nor terminals. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteKeepalive
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal StagedTerminalComplete CompleteCarrier

theorem changed (change : KeepaliveChange history ledger pid r after)
    (complete : Complete history ledger) : Complete (history ++ [.keepalivePrepared pid r]) after := by
  have quiet : StagedTerminalComplete.Quiet (.keepalivePrepared pid r) := by intro position; rfl
  cases change with
  | unchanged =>
    exact complete.append_quiet (fun _ member => List.mem_singleton.mp member ▸ quiet)
  | admitted generation stamp mtu =>
    exact (complete.admitted history.length (.staged generation pid stamp) [{mtu}]).append_quiet
      (fun _ member => List.mem_singleton.mp member ▸ quiet)

theorem normal (pid : PeerId) (before : Accounted h ledger debts locals w)
    (a b : Ambient) (v : WGWorld) (history : List Event) (ready : Bool)
    (run : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h = (.ok ((ready,v),b),history)) :
    let r : WGRunWitness Bool := ⟨ready,w,v,a,b⟩
    history = h ++ [.keepalivePrepared pid r] ∧
      r.Valid (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid) ∧
      ∃ after, Accounted history after debts locals v ∧ KeepaliveChange h ledger pid r after := by
  obtain ⟨position,native,after,entry,change,_⟩ := keepalive_normal pid before.entry a b v history ready run
  refine ⟨position,native,after,⟨entry,?_⟩,change⟩
  rw [position]
  exact changed change before.complete

theorem checked (pid : PeerId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) :
    StatePrefixPreserves (Carrier debts locals) Safe (CausalJournal.keepalivePrepare pid) := by
  intro w ambient history before
  obtain ⟨ledger,accounted⟩ := before
  cases performed : runWGPrefix (CausalJournal.keepalivePrepare pid) w ambient history with
  | mk outcome last =>
    change runPrefix ((CausalJournal.keepalivePrepare pid).run w) ambient history = _ at performed
    rw [performed]
    cases outcome with
    | error stop =>
      obtain ⟨same,_,_⟩ := keepalive_stopped pid accounted.entry ambient last stop performed
      subst last
      exact ⟨[],by simp,accountSafe _ _ _ accounted,True.intro⟩
    | ok out =>
      obtain ⟨⟨value,v⟩,clock⟩ := out
      obtain ⟨position,_,after,next,_⟩ := normal pid accounted ambient clock v last value performed
      exact ⟨[.keepalivePrepared pid ⟨value,w,v,ambient,clock⟩],position,
        accountSafe _ _ _ next,after,next⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteKeepalive
