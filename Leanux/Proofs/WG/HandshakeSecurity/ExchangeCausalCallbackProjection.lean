import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietActors
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNestedFrames
import Leanux.Proofs.WG.TransmitSecurity.JournalResponderProjection

/-! Native endpoints and independently proved history frames for the enriched
callbacks. Hiding receipts requires explicit exclusions of their constructors. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausal.Callbacks
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity AuthenticatedEffects
open CausalJournal Queues

private theorem state_erases (ρ : E → Option F) (g : WGPrefix E α) (t : WGPrefix F α)
    (a : WG.M α) (project : StateProjectsPrefix ρ id g t) (native : ErasesStatePrefix t a) :
    ErasesStatePrefix g a := by
  intro w b h
  have result := congrArg Prod.fst (project w b h)
  change (runStatePrefix t w b (h.filterMap ρ)).1 = (runStatePrefix g w b h).1.map id at result
  simpa only [runStatePrefix,runPrefix,StateT.run,Except.map_id,id_eq] using result.symm.trans (native w b (h.filterMap ρ))

private theorem state_native (ρ : E → Option F) (g : WGPrefix E α) (a : WG.M α)
    (project : StateProjectsPrefix ρ id g (liftWGPrefix a)) : ErasesStatePrefix g a :=
  state_erases ρ g _ a project (erasesStatePrefix_lift a)

theorem selection (ρ : Event → Option F)
    (taken : ∀ r, ρ (.stagingTaken r) = none)
    (selected : ∀ pid r, ρ (.old (.responder (.selected pid r))) = none) (pid : PeerId) :
    StateProjectsPrefix ρ id (CausalJournal.selection pid) (liftWGPrefix (Responder.selectionPrefix pid)) :=
  Exchange.quiet_native_projection ρ _ _
    (receiptWGObserved_erases (StagedConservation.Take.observed_erases _ pid) _)
    (CallbackQuiet.selection ρ taken selected pid).2

theorem create (ρ : Event → Option F) (tx : ∀ e, ρ (txEvent e) = none)
    (disposal : ∀ e, ρ (.stagedDisposal e) = none)
    (terminal : ∀ e, ρ (.terminalDrop e) = none) (pid : PeerId) (item : List SkbId) :
    StateProjectsPrefix ρ id (CausalJournal.create pid item) (liftWGPrefix (createData pid item)) :=
  Exchange.quiet_native_projection ρ _ _
    (state_erases old? _ _ _ (CausalJournal.create_projects pid item)
      (state_native Journal.responder? _ _ (Journal.ResponderProjection.create pid item)))
    (CallbackQuiet.create ρ tx disposal terminal pid item).2

theorem encrypt (ρ : Event → Option F)
    (encrypted : ∀ r, ρ (.old (.encrypted r)) = none)
    (disposal : ∀ e, ρ (.stagedDisposal e) = none)
    (returned : ∀ item r, ρ (.old (.encryptionReturn item r)) = none)
    (item : Option (List SkbId)) :
    ProjectsPrefix ρ id (CausalJournal.encrypt item) (liftPrefix (RxWorkers.encryptStepTailSource item)) := by
  apply (CallbackQuiet.encrypt ρ encrypted disposal returned item).2.project
  intro w h
  have old := congrArg Prod.fst (CausalJournal.encrypt_projects item w h)
  have native := congrArg Prod.fst (Journal.ResponderProjection.encrypt item w (h.filterMap old?))
  change (runPrefix (Journal.encrypt item) w (h.filterMap old?)).1 =
    (runPrefix (CausalJournal.encrypt item) w h).1.map id at old
  change (RxWorkers.encryptStepTailSource item).run w =
    (runPrefix (Journal.encrypt item) w (h.filterMap old?)).1.map id at native
  simp only [Except.map_id,id_eq] at old native
  exact old.symm.trans native.symm

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausal.Callbacks
