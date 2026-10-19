import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteSocket

/-! The unsupported-family demand is derived from the same actual peer read
used by the native send guard. It is paired with that send's chosen ledger
successor, rather than an independently selected terminal witness. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete
open HandshakeSecurity.StagedConservation

theorem peer_family (peer : RunWitness Peer)
    (valid : peer.Valid (liftWG (getPeer pid))) :
    endpointFamily peer.before.wg pid = (peer.value.endpoint.map (·.family)).getD 0 := by
  change (liftWG (getPeer pid)).run peer.before = .ok (peer.value,peer.after) at valid
  rw [liftWG_run] at valid
  cases native : ((getPeer pid).run peer.before.wg).run peer.before.ambient with
  | error stop => simp [native,Except.map] at valid
  | ok out =>
    rcases out with ⟨⟨value,wg⟩,ambient⟩
    cases hd : peer.before.wg.dev with
    | none =>
      simp [getPeer,getDev,hd,invariant,AmbientM.invariant] at native
      cases native
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [getPeer,getDev,hd,hp,invariant,AmbientM.invariant] at native
        cases native
      | some old =>
        have returned : ((getPeer pid).run peer.before.wg).run peer.before.ambient =
            .ok ((old,peer.before.wg),peer.before.ambient) := by
          simp [getPeer,getDev,hd,hp] <;> rfl
        rw [returned] at native
        cases native
        simp only [returned,Except.map,Except.ok.injEq,Prod.mk.injEq] at valid
        simp only [endpointFamily,hd,Option.bind_some,hp,valid.1]

theorem unsupported_cut
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger)
    (packetAt : PacketAt skb packet w)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ middle))
    (not4 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET)
    (not6 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET6) :
    let v := CompletionFirstTerminal.refusedWorld u
    let receipt : SendResult.Receipt := ⟨context.pid,skb,packet,⟨false,w,v⟩⟩
    let prior := history ++ middle.map FirstTerminal.encode
    let outcome := Staged.Obligations.Terminal.sendRefused prior.length
    let journal := prior ++ [CausalJournal.Event.sendResult receipt]
    ∃ chosen : Binding, chosen ∈ context.bindings ∧ chosen.skb = skb ∧
      runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history =
        (.ok (false,v),journal) ∧
      Owned context (.sending rest) journal (settle [chosen.ticket] outcome ledger)
        (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) v ∧
      Complete journal (settle [chosen.ticket] outcome ledger) := by
  dsimp only
  obtain ⟨chosen,member,head,noSocket,source,after⟩ :=
    indexed_unsupported_advanced before packetAt read not4 not6
  refine ⟨chosen,member,head,source,after,?_⟩
  have prior := complete.append_quiet (completion_events_quiet noSocket)
  have entry := before.append (middle.map FirstTerminal.encode) (by
    intro event inside
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp inside
    exact completion_encode_births original)
  have pending := (entry.cursor.assigned chosen member).1 (by simp [head])
  have facts := peer_cut_facts context.pid w u peer _ _ read
  have family := peer_family peer facts.1
  rw [facts.2] at family
  apply settle_singleton entry.entry prior pending
  apply unsupported_result_demand
  change ¬ (endpointFamily w.wg context.pid = AF_INET ∨ endpointFamily w.wg context.pid = AF_INET6)
  rw [family]
  exact not_or_intro not4 not6

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
