import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCompletionResult

/-! All branches of the actual send callback preserve logical prefix safety.
The original result-aware theorem supplies the same indexed terminal/Stop
postcondition; cuts are established from the captured read and socket source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
open CompletionFirstTerminal HandshakeSecurity.StagedConservation
variable {Safe : List CausalJournal.Event → Prop} {packet : RunWitness DataPacket}

theorem family_cuts (accountSafe : AccountSafe Safe)
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger) (packetAt : PacketAt skb packet w) (ipv4 : Bool)
    (read : runPrefix (captureObserved (TransmitSecurity.Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (family : SelectedFamily ipv4 peer) :
    ∃ suffix, (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).2 =
      history ++ suffix ∧ Cuts Safe history suffix := by
  let prior := history ++ readEvents.map FirstTerminal.encode
  have readQuiet := mapped_quiet_suffix (read_ledger_quiet context.pid) w history readEvents (congrArg Prod.snd read)
  have readCuts := quiet_cuts accountSafe before complete readQuiet
  have readWorld := FirstTerminal.peer_cut_world context.pid w u peer _ _ read
  have same : (familyWorld ipv4 u).wg = w.wg := by cases ipv4 <;> exact readWorld
  have kept := (before.append (readEvents.map FirstTerminal.encode) (by
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact completion_encode_births original)).sameWG same
  have priorComplete := Converse.extension complete rfl readQuiet
  have appends : Appends (socketBody context.pid packet peer ipv4) := by
    cases ipv4 <;> exact Appends.focus _ _ _
  obtain ⟨events,grown⟩ := appends (familyWorld ipv4 u) (prior.filterMap CausalJournal.completion?)
  cases run : runPrefix (socketBody context.pid packet peer ipv4) (familyWorld ipv4 u)
      (prior.filterMap CausalJournal.completion?) with
  | mk result journal =>
    rw [run] at grown
    dsimp only at grown
    cases result with
    | error reason =>
      have failed : runPrefix (socketBody context.pid packet peer ipv4) (familyWorld ipv4 u)
          (prior.filterMap CausalJournal.completion?) =
          (.error reason,prior.filterMap CausalJournal.completion? ++ events) := by rw [run,grown]
      obtain ⟨observed,_,_,cuts⟩ := socket_failure_cuts accountSafe before complete ipv4 read family failed
      exact ⟨readEvents.map FirstTerminal.encode ++ events.map FirstTerminal.encode,
        by rw [observed]; simp only [List.append_assoc],cuts⟩
    | ok result =>
      obtain ⟨ret,v⟩ := result
      have performed : runPrefix (socketBody context.pid packet peer ipv4) (familyWorld ipv4 u)
          (prior.filterMap CausalJournal.completion?) =
          (.ok (ret,v),prior.filterMap CausalJournal.completion? ++ events) := by rw [run,grown]
      obtain ⟨chosen,_,_,paired,suffix,extended,cuts,result⟩ := inner_accounting_cuts accountSafe kept priorComplete
        (packetAt.sameWG same) (peer_cut_facts context.pid w u peer _ _ read).1 performed
      have source := family_send_run context.pid skb packet peer ipv4 w u history readEvents read family
      rw [← source] at paired extended result
      have joined := readCuts.append cuts
      have extendedFull : (runPrefix (FirstTerminal.focused (TransmitSecurity.Completion.send context.pid skb packet)) w history).2 =
          history ++ (readEvents.map FirstTerminal.encode ++ suffix) := by
        simpa only [List.append_assoc] using extended
      have wrapper : CausalJournal.completionOps.send context.pid skb packet =
          SendResult.observed CausalJournal.Event.sendResult
            (FirstTerminal.focused (TransmitSecurity.Completion.send context.pid skb packet)) context.pid skb packet := rfl
      cases innerRun : runPrefix (FirstTerminal.focused (TransmitSecurity.Completion.send context.pid skb packet)) w history with
      | mk outcome last =>
        rw [innerRun] at paired extendedFull result
        dsimp only at paired extendedFull
        cases outcome with
        | error reason =>
          refine ⟨readEvents.map FirstTerminal.encode ++ suffix,?_,joined⟩
          simpa only [wrapper,SendResult.observed,runPrefix_receiptObserved,innerRun] using extendedFull
        | ok out =>
          obtain ⟨sent,after⟩ := out
          have actual : runPrefix (FirstTerminal.focused (TransmitSecurity.Completion.send context.pid skb packet)) w history =
              (.ok (sent,after),history ++ (readEvents.map FirstTerminal.encode ++ suffix)) := by
            rw [innerRun,extendedFull]
          have owned : Owned context (.sending rest) last
              (settle [chosen.ticket] (.socket (prior ++ events.map FirstTerminal.encode).length (ret == 0)) ledger)
              (⟨chosen.ticket,chosen.position,chosen.ordinal,
                .socket (prior ++ events.map FirstTerminal.encode).length (ret == 0)⟩ :: debts) after := result
          rw [extendedFull] at owned paired
          obtain ⟨observed,_,_,allCuts⟩ := supported_result_cuts accountSafe (Converse.supported_entry read family)
            actual owned paired joined
          refine ⟨(readEvents.map FirstTerminal.encode ++ suffix) ++ [_],?_,allCuts⟩
          rw [observed]
          simp only [List.append_assoc]

theorem send_cuts (accountSafe : AccountSafe Safe)
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger) (packetAt : PacketAt skb packet w) :
    ∃ suffix, (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).2 =
      history ++ suffix ∧ Cuts Safe history suffix := by
  have appends : Appends (captureObserved (TransmitSecurity.Completion.access (getPeerMixed context.pid))) :=
    Appends.captureObserved (Appends.focus _ _ _)
  obtain ⟨events,extension⟩ := appends w (history.filterMap CausalJournal.completion?)
  cases run : runPrefix (captureObserved (TransmitSecurity.Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) with
  | mk result journal =>
    rw [run] at extension
    dsimp only at extension
    cases result with
    | error reason =>
      have failed : runPrefix (captureObserved (TransmitSecurity.Completion.access (getPeerMixed context.pid))) w
          (history.filterMap CausalJournal.completion?) =
          (.error reason,history.filterMap CausalJournal.completion? ++ events) := by rw [run,extension]
      obtain ⟨observed,_,_,cuts⟩ := read_failure_cuts (packet := packet) accountSafe before complete failed
      exact ⟨events.map FirstTerminal.encode,by rw [observed],cuts⟩
    | ok out =>
      obtain ⟨peer,u⟩ := out
      have read : runPrefix (captureObserved (TransmitSecurity.Completion.access (getPeerMixed context.pid))) w
          (history.filterMap CausalJournal.completion?) =
          (.ok (peer,u),history.filterMap CausalJournal.completion? ++ events) := by rw [run,extension]
      by_cases family4 : (peer.value.endpoint.map (·.family)).getD 0 = AF_INET
      · exact family_cuts accountSafe before complete packetAt true read family4
      · by_cases family6 : (peer.value.endpoint.map (·.family)).getD 0 = AF_INET6
        · exact family_cuts accountSafe before complete packetAt false read ⟨family4,family6⟩
        · obtain ⟨_,_,_,observed,_,_,cuts⟩ := unsupported_cuts accountSafe before complete packetAt read family4 family6
          refine ⟨events.map FirstTerminal.encode ++ [_],?_,cuts⟩
          rw [observed]
          simp only [List.append_assoc]

theorem send (context : Context) (skb : SkbId) (rest : List SkbId)
    (packet : RunWitness DataPacket) (ledger : Ledger) (debts : List CleanupDebt)
    (accountSafe : AccountSafe Safe) :
    Checked (fun h w => Owned context (.sending (skb :: rest)) h ledger debts w ∧ Complete h ledger ∧ PacketAt skb packet w)
      Safe (Converse.Stopped context skb ledger debts) (CausalJournal.completionOps.send context.pid skb packet)
      (fun _ => Converse.Returned context skb rest ledger debts) :=
  Checked.of_cuts (Converse.send_checked context skb rest packet ledger debts)
    (fun _ _ before => send_cuts accountSafe before.1 before.2.1 before.2.2)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
