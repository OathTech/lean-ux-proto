import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverInitialized
import Leanux.Proofs.WG.TransmitSecurity.JournalResponderProjection
import Leanux.Proofs.WG.AuthenticatedEffects.TransportJournalInitialized

/-! Responder-current chronology and authenticated confirmation share one
initialized source journal. The projection preserves internal event order;
native endpoint erasure alone is not used to identify two histories. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues TransmitSecurity AuthenticatedEffects

/-- The successful native confirmation is strictly before the selected event.
Its immediately preceding replay receipt contains the actual earlier AEAD
publication. The allocation here is measured at confirmation; connecting it
to the key at the earlier AEAD requires the independent lifetime carrier. -/
def PriorAuthenticatedConfirmation (pre : List Journal.Event) (allocation : Nat) : Prop :=
  ∃ left right event pid kid, ∃ r : WGRunWitness Bool, ∃ core : KeyCore,
    pre = left ++ event :: right ∧
    Journal.responder? event = some (.confirmed pid kid r) ∧
    r.Valid (receivedWithKeypair pid kid) ∧ r.value = true ∧
    keyCoreAt r.before kid = some core ∧ core.allocation = allocation ∧
    ∃ earlier counter, left = earlier ++ [Journal.Event.replay counter] ∧
      counter.packet.peer = pid ∧ counter.packet.keypair = kid ∧
      counter.run.value = true ∧
      TransportReplay.Certified (earlier.filterMap Journal.origin?) counter

theorem journal_history (trace : Runner.Trace) (placeholders : Bool) :
    (runPrefixOuter (DriverCuts.execute trace placeholders) []).2 =
      (runPrefixOuter (Journal.execute trace placeholders) []).2.filterMap Journal.responder? :=
  congrArg Prod.snd (Journal.ResponderProjection.execute trace placeholders [])

/-- The selected responder's allocation has a successful earlier confirmation
in the same initialized source journal, and that exact call follows its actual
authenticated, replay-accepted transport packet. H1 remains explicit; no
incoming reachability or authentication premise is assumed. -/
theorem journal_selected_authenticated_confirmation
    (H1 : H1ResponderCurrentEdges) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Journal.Event) (event : Journal.Event) (pid : PeerId)
    (r : WGRunWitness (Option (Peer × Option KeypairId)))
    (position : (runPrefixOuter (Journal.execute trace placeholders) []).2 = pre ++ event :: post)
    (recorded : Journal.responder? event = some (.selected pid r))
    (p : Peer) (kid : KeypairId) (selected : r.value = some (p,some kid))
    (core : KeyCore) (material : pool r.after kid = some core) (responder : core.initiator = false) :
    PriorAuthenticatedConfirmation pre core.allocation := by
  have projected : (runPrefixOuter (DriverCuts.execute trace placeholders) []).2 =
      pre.filterMap Journal.responder? ++ .selected pid r :: post.filterMap Journal.responder? := by
    rw [journal_history,position,List.filterMap_append,List.filterMap_cons,recorded]
  have prior := DriverCuts.initialized_selected H1 trace placeholders _ _ pid r
    projected p kid selected core material responder
  obtain ⟨cut,inside,label⟩ := List.mem_flatMap.mp prior
  cases cut with
  | selected _ _ => cases label
  | session _ _ => cases label
  | confirmed peer slot receipt =>
    change core.allocation ∈ confirmedAt receipt.before slot receipt.value at label
    cases accepted : receipt.value with
    | false => simp [confirmedAt,accepted] at label
    | true =>
      cases resident : keyCoreAt receipt.before slot with
      | none => simp [confirmedAt,accepted,resident] at label
      | some previous =>
        have allocation : previous.allocation = core.allocation := by
          have same : core.allocation = previous.allocation := by
            simpa [confirmedAt,accepted,resident] using label
          exact same.symm
        obtain ⟨source,member,decoded⟩ := List.mem_filterMap.mp inside
        obtain ⟨left,right,split⟩ := List.mem_iff_append.mp member
        have occurrence : (runPrefixOuter (Journal.execute trace placeholders) []).2 =
            left ++ source :: (right ++ event :: post) := by
          rw [position,split]
          simp only [List.append_assoc,List.cons_append]
        obtain ⟨valid,authenticated⟩ := TransportJournal.confirmation_authenticated
          trace placeholders left _ source peer slot receipt occurrence decoded
        exact ⟨left,right,source,peer,slot,receipt,previous,split,decoded,
          valid,accepted,resident,allocation,authenticated⟩

end Leanux.Proofs.WG.HandshakeSecurity.Responder
