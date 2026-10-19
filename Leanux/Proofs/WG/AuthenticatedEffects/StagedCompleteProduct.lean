import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTransmitCuts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocatedCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeContracts

/-! Product-state composition retains the complete packet ledger and its
native allocation companion on the same observed execution. Stop safety names
the accounted source cut and never fabricates a returned native world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open StagedTerminalComplete

abbrev Carrier (h : List Event) (w : World) : Prop :=
  CompleteAllocated.Carrier [] [] h w.wg w.ambient

def Safe (h : List Event) : Prop := ∃ debts, CompleteTransmit.Safe debts h

theorem account_safe (ledger : Ledger) (h : List Event) (w : WGWorld)
    (before : CompleteCarrier.Accounted h ledger [] [] w) : Safe h := ⟨[],.accounted ledger [] h w before⟩

theorem source_state {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
    {body : WGPrefix Event α}
    (checked : CompletePassive.Checked debts locals (CompleteTransmit.Safe debts) body) :
    CompletePassive.Checked debts locals Safe body := by
  intro w a h before
  obtain ⟨suffix,extended,safe,kept⟩ := checked w a h before
  exact ⟨suffix,extended,⟨debts,safe⟩,kept⟩

theorem source_product {debts : List AllocatedObligation.CleanupDebt}
    {P : List Event → World → Prop} {Q : α → List Event → World → Prop} {body : PrefixM Event α}
    (checked : PrefixEnsures P (CompleteTransmit.Safe debts) body Q) : PrefixEnsures P Safe body Q := by
  intro w h before
  obtain ⟨suffix,extended,safe,kept⟩ := checked w h before
  exact ⟨suffix,extended,⟨debts,safe⟩,kept⟩

theorem carrier_safe (h : List Event) (w : World) (before : Carrier h w) : Safe h := by
  obtain ⟨ledger,accounted⟩ := before.1
  exact account_safe ledger h w.wg accounted

abbrev Checked (action : PrefixM Event α) : Prop := PrefixPreserves Carrier Safe action

abbrev StateChecked (action : WGPrefix Event α) : Prop := CompleteAllocated.Checked [] [] Safe action

theorem state {body : WGPrefix Event α} (checked : StateChecked body) :
    Checked (liftWGObserver body) := checked.liftWGObserver

theorem pair {body : WGPrefix Event α} {native : WG.M α}
    (checked : CompletePassive.Checked [] [] Safe body) (erases : ErasesStatePrefix body native)
    (allocated : Preserves StackOwnership.Allocated native) : StateChecked body :=
  CompleteAllocated.pair Safe checked erases allocated

theorem pair_product {body : PrefixM Event α} {native : Leanux.M α}
    (checked : PrefixPreserves (fun h w => CompleteCarrier.Carrier [] [] h w.wg w.ambient) Safe body)
    (erases : ErasesPrefix body native)
    (allocated : Preserves (fun w : World => StackOwnership.Allocated w.wg) native) : Checked body := by
  intro w h before
  obtain ⟨suffix,extended,safe,kept⟩ := checked w h before.1
  refine ⟨suffix,extended,safe,?_⟩
  cases performed : (runPrefix body w h).1 with
  | error reason => trivial
  | ok out =>
    obtain ⟨value,v⟩ := out
    rw [performed] at kept
    exact ⟨kept,(hoare_iff_run _ _ _).mp allocated w value v before.2
      ((erases w h).symm.trans performed)⟩

theorem wg (native : WG.M α) (checked : StateChecked (liftWGPrefix native)) :
    Checked (liftPrefix (liftWG native)) := by
  simpa only [liftWGObserver_lift] using state checked

theorem pure_checked (value : α) : Checked (pure value) :=
  PrefixPreserves.pure carrier_safe value

theorem bind_checked {body : PrefixM Event α} {next : α → PrefixM Event β}
    (head : Checked body) (tail : ∀ value, Checked (next value)) : Checked (body >>= next) :=
  PrefixPreserves.bind head tail

theorem conditional (p : Prop) [Decidable p] {left right : PrefixM Event α}
    (yes : p → Checked left) (no : ¬p → Checked right) : Checked (if p then left else right) := by
  by_cases test : p <;> simp only [test,↓reduceIte]
  · exact yes test
  · exact no test

theorem list {α β : Type} (xs : List α) (initial : β)
    (body : α → β → PrefixM Event (ForInStep β))
    (checked : ∀ value acc, Checked (body value acc)) : Checked (forIn xs initial body) :=
  PrefixPreserves.forIn xs initial body carrier_safe checked

theorem native (action : Leanux.M α) (keeps : ∀ h, Preserves (Carrier h) action) :
    Checked (liftPrefix action) :=
  PrefixEnsures.lift action carrier_safe
    (fun h w value v before run => (hoare_iff_run _ _ _).mp (keeps h) w value v before run)

theorem emit (event : Event) (birth : birthPackets event = []) (terminal : Quiet event) :
    Checked (emitPrefix event) := by
  have keep : ∀ h w, Carrier h w → Carrier (h ++ [event]) w := by
    intro h w before
    obtain ⟨⟨ledger,accounted⟩,allocated⟩ := before
    exact ⟨⟨ledger,accounted.append_quiet [event] (by simpa using birth) (by simpa using terminal)⟩,allocated⟩
  intro w h before
  exact ⟨[event],rfl,carrier_safe _ w (keep h w before),keep h w before⟩

theorem scope (cause : Cause) (body : CausalScope.Token Cause → PrefixM Event α)
    (checked : ∀ token, Checked (body token)) : Checked (CausalScope.prefixScope Event.scope cause body) := by
  intro w h before
  exact bind_checked (emit (.scope (.entered ⟨h.length,cause⟩)) rfl (fun _ => rfl))
    (fun _ => bind_checked (checked ⟨h.length,cause⟩) (fun value =>
      bind_checked (emit (.scope (.exited h.length)) rfl (fun _ => rfl))
        (fun _ => pure_checked value))) w h before

theorem capture {body : PrefixM Event α} (checked : Checked body) :
    Checked (captureObserved body) := checked.captureObserved

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
