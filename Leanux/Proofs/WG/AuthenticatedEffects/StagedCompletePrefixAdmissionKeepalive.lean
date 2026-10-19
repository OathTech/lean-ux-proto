import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixState
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteKeepalive

/-! Keepalive preparation has one actual completed receipt or no appended
event on Stop. Its same-ledger successor certifies every newly crossed
journal prefix; no native reachability is inferred from this certificate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Admission
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal CompleteCarrier

theorem keepalive_cuts (pid : PeerId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
    (w : WGWorld) (a : Ambient) (h : List Event) (before : Carrier debts locals h w a) :
    ∃ suffix, (runWGPrefix (CausalJournal.keepalivePrepare pid) w a h).2 = h ++ suffix ∧
      Cuts Safe h suffix := by
  obtain ⟨ledger,accounted⟩ := before
  cases performed : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h with
  | mk outcome last =>
    cases outcome with
    | error stop =>
      obtain ⟨same,_,_⟩ := keepalive_stopped pid accounted.entry a last stop performed
      subst last
      exact ⟨[],by simp,Cuts.nil (accountSafe _ _ _ accounted)⟩
    | ok out =>
      obtain ⟨⟨ready,v⟩,b⟩ := out
      obtain ⟨position,_,after,next,_⟩ := CompleteKeepalive.normal pid accounted a b v last ready performed
      refine ⟨[.keepalivePrepared pid ⟨ready,w,v,a,b⟩],position,?_⟩
      exact Cuts.singleton (accountSafe _ _ _ accounted) (position ▸ accountSafe after last v next)

theorem keepalive (pid : PeerId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) :
    StateEnsures (Carrier debts locals) Safe (CausalJournal.keepalivePrepare pid)
      (fun _ => Carrier debts locals) :=
  StateEnsures.of_cuts (CompleteKeepalive.checked pid Safe accountSafe)
    (keepalive_cuts pid Safe accountSafe)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Admission
