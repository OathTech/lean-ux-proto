import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionSocket

/-! The real byte-accounting suffix retains the socket's first terminal and
the complete selected local. A Stop is certified at this suffix's actual entry,
after the inner receipt, rather than at a pre-socket pending state. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CompletionCuts

private theorem accounting_peer_ownership (pid : PeerId) (size : Nat) :
    SameView ownershipPointView (do
      let p ← getPeer pid
      setPeer pid {p with txBytes := p.txBytes + size}) := by
  intro initial
  apply hoare_bind _ _ (ownership_getPeer (fun s => s = initial) pid)
  intro p
  exact ownership_setPeer (fun s => s = initial) pid _

theorem accounting_ownership (pid : PeerId) (packet : RunWitness DataPacket) (ret : Int) :
    SameView (fun w : World => ownershipPointView w.wg) (FirstTerminal.accountingNative pid packet ret) := by
  have branch : SameView ownershipPointView (branch .sendSkbOk (ret == 0) : WG.M Bool) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    cases run
    rfl
  have lift_frame {α} (action : WG.M α) (frame : SameView ownershipPointView action) :=
    sameView_liftWG (fun w : World => ownershipPointView w.wg) ownershipPointView action frame
      (fun _ _ _ same => same)
  intro initial
  unfold FirstTerminal.accountingNative
  apply preserves_bind (lift_frame _ branch initial)
  intro sent
  cases sent
  · exact preserves_pure _
  · apply preserves_bind (lift_frame _ (accounting_peer_ownership pid packet.value.bytes.length) initial)
    intro _
    exact preserves_pure _

theorem quiet_result_checked (site : Site) (source : site.action = discard action)
    (appends : Appends action) (quiet : HistoryFrame ledgerEvent? action)
    (erases : ErasesPrefix action native)
    (normal : ∀ w history value v, State context phase history w →
      native.run w = .ok (value,v) → State context phase history v) :
    Ensures (State context phase) (Stopped context) action (fun _ => State context phase) := by
  intro w history before
  obtain ⟨suffix,grown⟩ := appends w history
  refine ⟨suffix,grown,?_⟩
  cases run : runPrefix action w history with
  | mk result after =>
    cases result with
    | error reason =>
      refine ⟨⟨phase,site,w,history,before,?_,?_,?_⟩⟩
      · exact ⟨suffix,by simpa only [run] using grown.symm⟩
      · rw [source,discard,runPrefix_bind,run]
      · simpa only [run,ledger_filter] using quiet w history
    | ok result =>
      obtain ⟨value,v⟩ := result
      have kept := normal w history value v before
        ((erases w history).symm.trans (congrArg Prod.fst run))
      simp only [run] at grown
      simpa only [grown] using kept.append suffix

theorem accounting_checked (context : Context) (phase : Phase)
    (packet : RunWitness DataPacket) (ret : Int) :
    Ensures (State context phase) (Stopped context)
      (FirstTerminal.focused (CompletionFirstTerminal.afterSocket context.pid packet ret))
      (fun _ => State context phase) := by
  apply quiet_result_checked (.accounting context.pid packet ret) rfl (Appends.focus _ _ _)
  · have inner : HistoryFrame (fun e => ledgerEvent? (FirstTerminal.encode e))
        (CompletionFirstTerminal.afterSocket context.pid packet ret) := by
      unfold CompletionFirstTerminal.afterSocket
      apply HistoryFrame.bind (HistoryFrame.lift _ _)
      intro sent
      cases sent
      · exact HistoryFrame.pure _ _
      · apply HistoryFrame.bind
        · exact focusPrefix_other _ _ _ (fun _ => rfl) _
        · intro _; exact HistoryFrame.pure _ _
    intro w h
    obtain ⟨suffix,grown⟩ := CompletionFirstTerminal.afterSocket_appends context.pid packet ret w
      (h.filterMap CausalJournal.completion?)
    have empty : suffix.filterMap (fun e => ledgerEvent? (FirstTerminal.encode e)) = [] := by
      have same := inner w (h.filterMap CausalJournal.completion?)
      rw [grown,List.filterMap_append] at same
      have lengths := congrArg List.length same
      simp only [List.length_append] at lengths
      exact List.eq_nil_of_length_eq_zero (by omega)
    have focused := focusPrefix_suffix FirstTerminal.encode CausalJournal.completion? _ w h
      (runPrefix (CompletionFirstTerminal.afterSocket context.pid packet ret) w
        (h.filterMap CausalJournal.completion?)).1 suffix (Prod.ext rfl grown)
    rw [focused]
    rw [List.filterMap_append,List.filterMap_map]
    change h.filterMap ledgerEvent? ++ suffix.filterMap (fun e => ledgerEvent? (FirstTerminal.encode e)) = _
    rw [empty,List.append_nil]
  · exact focusPrefix_erases _ _ (FirstTerminal.accounting_erases context.pid packet ret)
  · intro w history value v before run
    exact before.views
      ((ProjectedAction.iff_run _ _ _).mp (FirstTerminal.accounting_snapshot context.pid packet ret) w value v run)
      ((ProjectedAction.iff_run _ _ _).mp (accounting_ownership context.pid packet ret) w value v run)

/-- The exact inner socket followed by accounting retains the socket event
on both return and Stop. Any failed frontier starts after that first terminal,
with the same selected batch and its terminal cleanup debt. -/
theorem inner_accounting_checked (before : State context (.sending (skb :: rest)) history w)
    (packetAt : PacketAt skb packet w)
    (peerValid : peer.Valid (liftWG (getPeer context.pid)))
    (performed : runPrefix (CompletionFirstTerminal.socketBody context.pid packet peer ipv4) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (ret,v),history.filterMap CausalJournal.completion? ++ middle)) :
    let journal := (history ++ middle.map FirstTerminal.encode) ++
      [CausalJournal.Event.old (.socket ⟨context.pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩)]
    let actual := FirstTerminal.focused (Completion.socket context.pid skb packet peer ipv4 >>=
      CompletionFirstTerminal.afterSocket context.pid packet)
    ∃ suffix, (runPrefix actual w history).2 = journal ++ suffix ∧
      match (runPrefix actual w history).1 with
      | .error reason => Stopped context reason (runPrefix actual w history).2
      | .ok (_,after) => State context (.sending rest) (runPrefix actual w history).2 after := by
  dsimp only
  obtain ⟨socket,owned⟩ := inner_advanced before packetAt peerValid performed
  rw [FirstTerminal.socket_accounting_factor,runPrefix_bind,socket]
  dsimp only
  obtain ⟨suffix,grown,result⟩ := accounting_checked context (.sending rest) packet ret v _ owned
  refine ⟨suffix,grown,?_⟩
  cases ended : (runPrefix (FirstTerminal.focused (CompletionFirstTerminal.afterSocket context.pid packet ret)) v
    ((history ++ middle.map FirstTerminal.encode) ++
      [CausalJournal.Event.old (.socket ⟨context.pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩)])).1 with
  | error reason => simpa only [ended] using result
  | ok out => rcases out with ⟨sent,after⟩; simpa only [ended] using result

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
