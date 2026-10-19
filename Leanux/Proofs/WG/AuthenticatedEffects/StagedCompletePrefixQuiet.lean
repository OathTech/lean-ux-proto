import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixState
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProduct

/-! The prefix certificate is added beside the existing full packet carrier.
Quiet emitters retain the same ledger, physical ownership and allocation
invariant. General event-producing actors need separate internal Cuts proofs;
this module does not upgrade their endpoint contracts automatically.

`History` records the logical Safe predicates. In particular, an existential
world in Safe.accounted is not thereby related to a native execution interval.
That source-cut relation remains an independent proof obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open StagedTerminalComplete

abbrev History (history : List Event) : Prop := All CompleteProduct.Safe history
abbrev ProductCarrier : List Event→World→Prop := With CompleteProduct.Carrier CompleteProduct.Safe

theorem initial (net bare : Bool) (w : World) (native : w.wg=Runner.initialWG net bare) :
    ProductCarrier [] w := by
  have carrier : CompleteProduct.Carrier [] w := by
    change CompleteAllocated.Carrier [] [] [] w.wg w.ambient
    rw [show w.wg=Runner.initialWG net bare from native]
    exact CompleteAllocated.initial net bare
  exact ⟨carrier,All.nil (CompleteProduct.carrier_safe [] w carrier)⟩

/-- Every quiet prefix is accounted by the same current ledger and snapshot.
Neither births nor terminal demands are allowed to use this passive rule. -/
theorem quiet_cuts (before : CompleteCarrier.Accounted history ledger debts locals w)
    (births : ∀ event∈suffix, birthPackets event=[])
    (terminals : ∀ event∈suffix, Quiet event) : Cuts CompleteProduct.Safe history suffix := by
  intro n _
  exact ⟨debts,.accounted ledger locals _ w (before.append_quiet (suffix.take n)
    (fun event member=>births event (List.mem_of_mem_take member))
    (fun event member=>terminals event (List.mem_of_mem_take member)))⟩

theorem product_emit (event : Event) (birth : birthPackets event=[]) (terminal : Quiet event) :
    Ensures CompleteProduct.Carrier CompleteProduct.Safe (emitPrefix event)
      (fun _=>CompleteProduct.Carrier) := by
  have keep : ∀ h w, CompleteProduct.Carrier h w→CompleteProduct.Carrier (h++[event]) w := by
    intro h w before
    obtain ⟨⟨ledger,accounted⟩,allocated⟩ := before
    exact ⟨⟨ledger,accounted.append_quiet [event] (by simpa using birth) (by simpa using terminal)⟩,allocated⟩
  exact Ensures.emit event (fun h w before=>CompleteProduct.carrier_safe _ w (keep h w before))
    keep

theorem state_emit (event : Event) (birth : birthPackets event=[]) (terminal : Quiet event) :
    StateEnsures (CompleteAllocated.Carrier debts locals) CompleteProduct.Safe (emitStatePrefix event)
      (fun _=>CompleteAllocated.Carrier debts locals) := by
  have keep : ∀ h w a, CompleteAllocated.Carrier debts locals h w a→
      CompleteAllocated.Carrier debts locals (h++[event]) w a := by
    intro h w a before
    obtain ⟨⟨ledger,accounted⟩,allocated⟩ := before
    exact ⟨⟨ledger,accounted.append_quiet [event] (by simpa using birth) (by simpa using terminal)⟩,allocated⟩
  apply StateEnsures.emit event
  · intro h w a before
    obtain ⟨ledger,accounted⟩ := (keep h w a before).1
    exact ⟨debts,.accounted ledger locals _ w accounted⟩
  · exact keep

/-- Native quiet leaves retain the full existing product invariant. Their
unchanged journal carries its previous certificate without reconstructing it. -/
theorem product_native (native : Leanux.M α)
    (keeps : ∀ h, Preserves (CompleteProduct.Carrier h) native) :
    Ensures CompleteProduct.Carrier CompleteProduct.Safe (liftPrefix native)
      (fun _=>CompleteProduct.Carrier) :=
  Ensures.lift native (fun h w value v before run=>
    (hoare_iff_run _ _ _).mp (keeps h) w value v before run)

/-- Integration boundary for an existing actor. The extra proof covers every
new event position in that actor's actual output, including its stopped run. -/
theorem product_of_cuts (endpoint : CompleteProduct.Checked body)
    (cuts : ∀ w h, CompleteProduct.Carrier h w→
      ∃ suffix, (runPrefix body w h).2=h++suffix ∧ Cuts CompleteProduct.Safe h suffix) :
    Ensures CompleteProduct.Carrier CompleteProduct.Safe body (fun _=>CompleteProduct.Carrier) :=
  Ensures.of_cuts endpoint cuts

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix
