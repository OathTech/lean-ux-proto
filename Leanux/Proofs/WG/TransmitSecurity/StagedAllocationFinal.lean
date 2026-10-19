import Leanux.Proofs.WG.TransmitSecurity.StagedInitialized
import Leanux.Proofs.WG.TransmitSecurity.BatchPayloadFinal

/-! The initialized positional origin carrier joins the actual plaintext batch
allocation. Equal plaintext values retain distinct staging occurrences. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects HandshakeSecurity

theorem old_member {history : List CausalJournal.Event} {event : Journal.Event}
    (member : event ∈ history.filterMap CausalJournal.old?) : CausalJournal.Event.old event ∈ history := by
  obtain ⟨e,inside,decoded⟩ := List.mem_filterMap.mp member
  cases e <;> simp only [CausalJournal.old?,Option.some.injEq,reduceCtorEq] at decoded
  subst event
  exact inside

theorem Safe.prefix (safe : Safe (history ++ suffix)) : Safe history := by
  intro pre event post position
  apply safe pre event (post ++ suffix)
  rw [position]
  simp only [List.append_assoc,List.cons_append]

/-- Allocation cannot substitute a packet from another route or peer. Every
initialized plaintext batch has ordered distinct prior routed/keepalive origins
for the exact peer allocation selected by the native staging call. -/
theorem initialized_allocation (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (packets : List DataPacket)
    (allocation : WGRunWitness (List SkbId))
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ .old (.allocated packets allocation) :: post) :
    allocation.Valid (packets.mapM newTxSkb) ∧
      ∃ pid peer slot selection generation,
        CausalJournal.Event.old (.responder (.selected pid selection)) ∈ pre ∧
        selection.Valid (Responder.selectionPrefix pid) ∧
        selection.value = some (peer,some slot) ∧
        Packets.epoch selection.before = some generation ∧
        Batch pre generation pid peer.internalId (packets.map DataPacket.plaintext) ∧
        BatchPayload.Shape pid slot peer.staged packets := by
  have payload := BatchPayload.final_initialized trace placeholders
  have allocated := payload (pre.filterMap CausalJournal.old?) (.allocated packets allocation)
    (post.filterMap CausalJournal.old?) (by
      rw [position]
      simp only [List.filterMap_append,List.filterMap_cons,CausalJournal.old?])
  obtain ⟨valid,pid,peer,slot,⟨selection,selected,selectionValid,value⟩,shape⟩ := allocated
  have selected := old_member selected
  obtain ⟨before,after,selectedAt⟩ := List.mem_iff_append.mp selected
  have origins := initialized trace placeholders
  rw [position] at origins
  have safePrefix := origins.prefix
  obtain ⟨generation,epoch,batch⟩ := safePrefix before (.old (.responder (.selected pid selection)))
    after selectedAt peer (some slot) value
  refine ⟨valid,pid,peer,slot,selection,generation,selected,selectionValid,value,epoch,?_,shape⟩
  rw [shape.1,selectedAt]
  exact batch.append_history _

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
