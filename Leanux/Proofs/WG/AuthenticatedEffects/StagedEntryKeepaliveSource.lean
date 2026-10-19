import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryKeepalive

/-! Actual keepalive preparation emits one completed native receipt, or stops
with its original accounted entry. Neither result assumes a successful native
call or invents a prepared packet before its real empty-queue allocation arm. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal RetirementSecurity

/-- The native source run and its exact appended receipt connect the newly
admitted ticket to this invocation, including true returns with no admission. -/
theorem keepalive_normal (pid : PeerId) (before : Inv h ledger debts locals w)
    (a b : Ambient) (v : WGWorld) (history : List Event) (ready : Bool)
    (run : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h = (.ok ((ready,v),b),history)) :
    let r : WGRunWitness Bool := ⟨ready,w,v,a,b⟩
    history = h ++ [.keepalivePrepared pid r] ∧
      r.Valid (OccurrenceHandshake.keepalivePrepare pid) ∧
      ∃ after, Inv history after debts locals v ∧ KeepaliveChange h ledger pid r after ∧
        ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
          (ticket,Status.terminal outcome) ∈ after := by
  dsimp only
  have observed := runWGPrefix_receiptWGObserved
    (liftWGPrefix (OccurrenceHandshake.keepalivePrepare pid)) (Event.keepalivePrepared pid) w a h
  rw [runWGPrefix_lift] at observed
  change runWGPrefix (CausalJournal.keepalivePrepare pid) w a h = _ at observed
  rw [observed] at run
  cases native : ((OccurrenceHandshake.keepalivePrepare pid).run w).run a with
  | error stop => rw [native] at run; cases run
  | ok out =>
    obtain ⟨⟨value,u⟩,c⟩ := out
    rw [native] at run
    cases run
    obtain ⟨after,inv,changed,retained⟩ := keepalive_receipt pid ⟨ready,w,v,a,b⟩ native before
    exact ⟨rfl,native,after,inv,changed,retained⟩

/-- Stop retains an explicit original entry cut and the exact unchanged event
prefix. No completed preparation receipt or keepalive birth is manufactured. -/
theorem keepalive_stopped (pid : PeerId) (before : Inv h ledger debts locals w)
    (a : Ambient) (history : List Event) (stop : Stop)
    (run : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h = (.error stop,history)) :
    history = h ∧ Inv history ledger debts locals w ∧
      ((OccurrenceHandshake.keepalivePrepare pid).run w).run a = .error stop := by
  have observed := runWGPrefix_receiptWGObserved
    (liftWGPrefix (OccurrenceHandshake.keepalivePrepare pid)) (Event.keepalivePrepared pid) w a h
  rw [runWGPrefix_lift] at observed
  change runWGPrefix (CausalJournal.keepalivePrepare pid) w a h = _ at observed
  rw [observed] at run
  cases native : ((OccurrenceHandshake.keepalivePrepare pid).run w).run a with
  | error actual =>
    rw [native] at run
    cases run
    exact ⟨rfl,before,rfl⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    rw [native] at run
    cases run

def KeepaliveNormal (_before : Inv h ledger debts locals w) (pid : PeerId)
    (a : Ambient) (value : Bool) (history : List Event) (v : WGWorld) (b : Ambient) : Prop :=
  let r : WGRunWitness Bool := ⟨value,w,v,a,b⟩
  history = h ++ [.keepalivePrepared pid r] ∧ r.Valid (OccurrenceHandshake.keepalivePrepare pid) ∧
    ∃ after, Inv history after debts locals v ∧ KeepaliveChange h ledger pid r after ∧
      ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
        (ticket,Status.terminal outcome) ∈ after

def KeepaliveCut (before : Inv h ledger debts locals w) (pid : PeerId) (a : Ambient)
    (history : List Event) : Prop :=
  (history = h ∧ Inv history ledger debts locals w) ∨
    ∃ value v b, KeepaliveNormal before pid a value history v b

/-- This is the complete observed preparation contract. Its stopped clause
names the retained native entry; its normal clause names the same successful
native receipt and exact fixed-ledger admission. -/
theorem keepalive_checked (pid : PeerId) (before : Inv h ledger debts locals w) (a : Ambient) :
    let result := runWGPrefix (CausalJournal.keepalivePrepare pid) w a h
    KeepaliveCut before pid a result.2 ∧
      match result.1 with
      | .error stop => result.2 = h ∧ Inv result.2 ledger debts locals w ∧
          ((OccurrenceHandshake.keepalivePrepare pid).run w).run a = .error stop
      | .ok ((value,v),b) => KeepaliveNormal before pid a value result.2 v b := by
  cases executed : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h with
  | mk result history =>
    cases result with
    | error stop =>
      have kept := keepalive_stopped pid before a history stop executed
      exact ⟨Or.inl ⟨kept.1,kept.2.1⟩,kept⟩
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      have kept := keepalive_normal pid before a b v history value executed
      exact ⟨Or.inr ⟨value,v,b,kept⟩,kept⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry
