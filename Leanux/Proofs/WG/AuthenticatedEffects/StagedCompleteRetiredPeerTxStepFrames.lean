import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxCompletionFrames
import Leanux.Proofs.WG.Queues.TxHolderStep

/-! The complete native TX step retains the exact account. Cached peek is
charge-neutral; readiness either returns idle or selects and pays its actual
batch, including any send-work reference acquired during completion. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders RetirementSecurity

theorem Account.tx_peek (account : Account holders carriers loans w)
    (pid : PeerId) (a b : Ambient)
    (run : ((txPeekSource pid).run w).run a = .ok ((first,v),b)) :
    Account holders carriers loans v ∧
      (∀ p, peerAt v pid = some p → p.txQueue.peeked = first) := by
  obtain ⟨d,p,queue,device,found,contents,cached,after⟩ := txPeek_effect pid a b run
  have input := (pinned_const
    _private.Leanux.Proofs.WG.Queues.TxHolderStep.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.peek_install)
    account.funded account.stable device found queue contents
  have peers : peerView v = peerView w := by
    rw [after]
    unfold peerView replacePeer
    simp only [device,Option.map_some,Option.bind_some]
    congr 1
    funext owner
    by_cases eq : pid = owner <;> simp_all [Std.TreeMap.getElem?_insert]
  refine ⟨⟨?_,account.upper.peer_view peers,?_⟩,?_⟩
  · simpa only [after,replacePeer] using input.1
  · simpa only [after,replacePeer] using input.2
  · intro q resident
    have eq : q = {p with txQueue := queue} := by
      simpa [peerAt,after,replacePeer] using resident.symm
    subst q
    exact cached

theorem Account.tx_completion (account : Account holders carriers loans w)
    (pid : PeerId) (item : List SkbId) (head : DataPacket) (a b : Ambient)
    (run : ((txCompletionSource pid item head).run w).run a = .ok (((),v),b)) :
    ∃ delta, delta.tx = [] ∧ Account (holders.absorb delta) carriers loans v := by
  rw [txCompletionSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨crypted,u,c,check,tail⟩ := run
  have same : u = w := by cases check; rfl
  subst u
  cases crypted with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at tail
    cases tail
    exact ⟨{},rfl,by simpa only [absorb,List.append_nil] using account⟩
  | true =>
    simp only [ite_true] at tail
    obtain ⟨delta,_,noTx,after⟩ := account.tx_complete pid item c b tail
    exact ⟨delta,noTx,after⟩

theorem Account.tx_ready (account : Account holders carriers loans w)
    (cached : ∀ p, peerAt w pid = some p → p.txQueue.peeked = first)
    (a b : Ambient)
    (run : ((txReadyTail pid first).run w).run a = .ok ((result,v),b)) :
    result = true ∧ ∃ chosen rest delta,
      TxSelected holders.tx pid chosen rest ∧ delta.tx = [] ∧
      Account ((holders.withoutTx rest).absorb delta) carriers loans v := by
  cases first with
  | none => simp only [txReadyTail] at run; cases run
  | some items =>
    cases headId : items.head? with
    | none => simp only [txReadyTail,headId] at run; cases run
    | some id =>
      rw [txReadyTail_factor pid items id headId,MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨head,u,c,readRun,tail⟩ := run
      obtain ⟨same,ambient,d,device,stored⟩ := Packets.getTxSkb_current id w u head a c readRun
      subst u
      subst c
      rw [MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,dropped,e,dropRun,tail⟩ := tail
      obtain ⟨dev,p,devAt,peerAt,_,_⟩ := txDrop_effect pid a e dropRun
      have cache := cached p (by simp [RetirementSecurity.peerAt,devAt,peerAt])
      obtain ⟨chosen,rest,selected,_,after⟩ := account.tx_select devAt peerAt cache a e dropRun
      rw [MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,completed,f,completeRun,disposeRun⟩ := tail
      obtain ⟨delta,noTx,completedAccount⟩ := after.tx_completion pid items head e f completeRun
      obtain ⟨resultEq,paid⟩ := completedAccount.tx_dispose items head.keypair f b
        (by simpa only [selected.slot] using disposeRun)
      exact ⟨resultEq,chosen,rest,delta,selected,noTx,paid⟩

theorem Account.tx_body (account : Account holders carriers loans w)
    (cached : ∀ p, peerAt w pid = some p → p.txQueue.peeked = first)
    (a b : Ambient)
    (run : ((TxDisposition.bodySource pid first).run w).run a = .ok ((result,v),b)) :
    ExactBoundary carriers loans v := by
  rw [tx_body_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,testRun,tail⟩ := run
  have same := (hoare_iff_run_ambient _ _ _).mp (ready_world_frame first (fun s => s = w))
    w a ready u c rfl testRun
  subst u
  cases ready with
  | false =>
    simp only [Bool.not_false,ite_true] at tail
    cases tail
    exact ⟨holders,account⟩
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    obtain ⟨_,chosen,rest,delta,_,_,after⟩ := account.tx_ready cached c b tail
    exact ⟨(holders.withoutTx rest).absorb delta,after⟩

/-- Every successful actual TX step preserves a single exact peer account;
the result does not require incoming readiness or an already selected batch. -/
theorem ExactBoundary.tx_step (pid : PeerId) : Preserves (ExactBoundary carriers loans) (txStep pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b input run
  obtain ⟨holders,account⟩ := input
  rw [txStep_peek_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨first,u,c,peek,body⟩ := run
  obtain ⟨after,cached⟩ := account.tx_peek pid a c peek
  exact after.tx_body cached c b body

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
