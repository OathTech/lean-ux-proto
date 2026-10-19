import Leanux.Proofs.WG.TransmitSecurity.StagedHandshakeOriginFrames

/-! Observation adapters preserve the actual staged-source carrier. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects.CausalJournal

theorem state_capture {action : WGPrefix Event α} (safe : StateSafe action) :
    StateSafe (captureWGObserved action) := StatePrefixPreserves.captureWGObserved safe

theorem state_receipt {action : WGPrefix Event α} (safe : StateSafe action)
    (record : WGRunWitness α → Event) (quiet : ∀ r, Quiet (record r)) :
    StateSafe (receiptWGObserved action record) :=
  StatePrefixEnsures.bind (state_capture safe) (fun r =>
    StatePrefixEnsures.bind (state_emit (record r) (quiet r)) (fun _ => state_pure r.value))

theorem state_current (body : Context → WGPrefix Event α) (safe : ∀ context, StateSafe (body context)) :
    StateSafe (AuthenticatedEffects.CausalEffects.atCurrent scope? body) := by
  intro w a h before
  exact safe (AuthenticatedEffects.CausalScope.current scope? h) w a h before

/-- A native frame and a separately proved history contract compose without
requiring an invariant at arbitrary observer callback arguments. -/
theorem state_history {action : WGPrefix Event α} {native : WG.M α}
    (history : Driver.StateHistorySafe Safe action) (erase : ErasesStatePrefix action native)
    (kept : ∀ h, Preserves (Inv h) native) : StateSafe action := by
  intro w a h before
  obtain ⟨suffix,position,safe,_⟩ := history w a h before.2
  refine ⟨suffix,position,safe,?_⟩
  cases outcome : (runPrefix (action.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have run : (native.run w).run a = .ok ((value,v),b) := (erase w a h).symm.trans outcome
    have inv := (hoare_iff_run_ambient _ _ _).mp (kept h) w a value v b before.1 run
    refine ⟨?_,safe⟩
    rw [position]
    exact inv.append suffix

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
