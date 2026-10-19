import Leanux.Proofs.WG.HandshakeSecurity.ReservationSelectionBinding
import Leanux.Proofs.WG.HandshakeSecurity.ResponderJournalConfirmation

/-! Actual responder encryption follows a successful confirmation of the same
allocation. Its triggering packet has the initialized replay and native AEAD
provenance already carried by this exact journal. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity AuthenticatedEffects

theorem PriorAuthenticatedConfirmation.append
    (before : PriorAuthenticatedConfirmation h allocation) :
    PriorAuthenticatedConfirmation (h ++ suffix) allocation := by
  obtain ⟨left,right,event,pid,kid,r,core,rfl,recorded,valid,accepted,resident,same,authenticated⟩ := before
  exact ⟨left,right ++ suffix,event,pid,kid,r,core,
    by simp only [List.append_assoc,List.cons_append],recorded,valid,accepted,resident,same,authenticated⟩

/-- The actual AEAD key's responder allocation was successfully confirmed
strictly before this encryption. The receive's AEAD provenance is exact;
receiving-key allocation continuity is not asserted by this endpoint. -/
theorem initialized_encryption_confirmation (H1 : H1ResponderCurrentEdges)
    (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Journal.Event) (r : WorkerEncryption.Receipt)
    (position : (runPrefixOuter (Journal.execute trace placeholders) []).2 = pre ++ .encrypted r :: post)
    (responder : r.cipher.keyRead.value.iAmTheInitiator = false) :
    r.Valid ∧ PriorAuthenticatedConfirmation pre r.cipher.keyRead.value.internalId := by
  obtain ⟨valid,left,right,pid,selected,peer,split,returned,resident⟩ :=
    ReservationSelection.initialized_encryption trace placeholders pre post r position
  have occurrence : (runPrefixOuter (Journal.execute trace placeholders) []).2 =
      left ++ Journal.Event.responder (.selected pid selected) :: (right ++ .encrypted r :: post) := by
    rw [position,split]
    simp only [List.append_assoc,List.cons_append]
  have prior := journal_selected_authenticated_confirmation H1 trace placeholders left _ _ pid selected
    occurrence rfl peer r.read.value.keypair returned (keyCore r.cipher.keyRead.value) resident responder
  refine ⟨valid,?_⟩
  rw [split]
  exact prior.append

/-- The final observer's exact old-event projection retains the same strict
encryption/confirmation chronology, including internally stopped prefixes. -/
theorem final_encryption_confirmation (H1 : H1ResponderCurrentEdges)
    (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Journal.Event) (r : WorkerEncryption.Receipt)
    (position : ((runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap
      CausalJournal.old?) = pre ++ .encrypted r :: post)
    (responder : r.cipher.keyRead.value.iAmTheInitiator = false) :
    r.Valid ∧ PriorAuthenticatedConfirmation pre r.cipher.keyRead.value.internalId := by
  have history := congrArg Prod.snd (CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  exact initialized_encryption_confirmation H1 trace placeholders pre post r (history.trans position) responder

end Leanux.Proofs.WG.HandshakeSecurity.Responder
