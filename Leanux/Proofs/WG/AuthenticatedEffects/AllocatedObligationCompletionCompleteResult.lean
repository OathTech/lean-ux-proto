import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteRefusal
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteAccounting

/-! A supported outer result adds no new terminal demand, even when false.
The endpoint-family fact is derived from this invocation's captured peer.
Preterminal failures retain completeness on the original pending ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete
open HandshakeSecurity.StagedConservation CompletionFirstTerminal

theorem supported_entry {history : List CausalJournal.Event}
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ events))
    (family : SelectedFamily ipv4 peer) :
    endpointFamily w.wg pid = AF_INET ∨ endpointFamily w.wg pid = AF_INET6 := by
  have facts := peer_cut_facts pid w u peer _ _ read
  have actual := peer_family peer facts.1
  rw [facts.2] at actual
  rw [actual]
  cases ipv4
  · exact Or.inr family.2
  · exact Or.inl family

theorem observed_complete
    (supported : endpointFamily w.wg pid = AF_INET ∨ endpointFamily w.wg pid = AF_INET6)
    (complete : Complete
      (runPrefix (FirstTerminal.focused (Completion.send pid skb packet)) w history).2 ledger) :
    Complete (runPrefix (CausalJournal.completionOps.send pid skb packet) w history).2 ledger := by
  have wrapper : CausalJournal.completionOps.send pid skb packet =
      SendResult.observed CausalJournal.Event.sendResult
        (FirstTerminal.focused (Completion.send pid skb packet)) pid skb packet := rfl
  simp only [wrapper,SendResult.observed,runPrefix_receiptObserved]
  cases run : runPrefix (FirstTerminal.focused (Completion.send pid skb packet)) w history with
  | mk result journal =>
    rw [run] at complete
    cases result with
    | error reason => exact complete
    | ok result =>
      obtain ⟨sent,after⟩ := result
      apply complete.append_quiet
      intro event member
      cases List.mem_singleton.mp member
      exact supported_result_quiet supported

theorem read_failure_complete
    (complete : Complete history ledger)
    (failed : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.error reason,history.filterMap CausalJournal.completion? ++ events)) :
    Complete (history ++ events.map FirstTerminal.encode) ledger :=
  extension complete rfl
    (mapped_quiet_suffix (read_ledger_quiet pid) w history events (congrArg Prod.snd failed))

theorem socket_failure_complete
    (complete : Complete history ledger)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (failed : runPrefix (socketBody pid packet peer ipv4) (familyWorld ipv4 u)
      ((history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?) =
        (.error reason,(history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion? ++ events)) :
    Complete ((history ++ readEvents.map FirstTerminal.encode) ++ events.map FirstTerminal.encode) ledger := by
  have prior := extension complete rfl
    (mapped_quiet_suffix (read_ledger_quiet pid) w history readEvents (congrArg Prod.snd read))
  exact extension prior rfl (mapped_quiet_suffix (socket_body_ledger_quiet pid packet peer ipv4)
    (familyWorld ipv4 u) (history ++ readEvents.map FirstTerminal.encode) events (congrArg Prod.snd failed))

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
