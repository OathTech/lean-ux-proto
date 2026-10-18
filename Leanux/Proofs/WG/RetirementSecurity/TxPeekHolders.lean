import Leanux.Proofs.WG.RetirementSecurity.SlotProjection
import Leanux.Proofs.WG.RetirementSecurity.TxHolderTransfer
import Leanux.Proofs.WG.Queues.TxDisposition

/-! The original TX worker's cached peek retains its batch reference. Only
the later drop setter removes a durable occurrence; moving items into the
queue's cached field does not acquire or pay a key reference. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG

def txPeekSource (pid : PeerId) : WG.M (Option (List SkbId)) := do
  let (first,queue) ← (← getPeer pid).txQueue.peek
  setPeer pid {(← getPeer pid) with txQueue := queue}
  return first

theorem txStep_peek_factor (pid : PeerId) : txStep pid = (do
    let first ← txPeekSource pid
    Queues.TxDisposition.bodySource pid first) := by
  rw [←Queues.TxDisposition.stepSource_eq]
  simp only [Queues.TxDisposition.stepSource,txPeekSource,bind_assoc,pure_bind]

theorem HolderAccount.peek_tx (account : HolderAccount temporary w) (pid : PeerId)
    (a b : Ambient)
    (run : ((txPeekSource pid).run w).run a = .ok ((first,v),b)) :
    HolderAccount temporary v ∧ ∃ before after,
      peerAt w pid = some before ∧ peerAt v pid = some after ∧
      first = before.txQueue.all.head? ∧ after.txQueue.all = before.txQueue.all ∧
      after.txQueue.peeked = first := by
  simp only [txPeekSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,pair,t,e,peekRun,q,s,f,readBack,_,r,g,setRun,finish⟩ := run
  obtain ⟨world,ambient,d,device,stored⟩ := Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  obtain ⟨selected,queue⟩ := pair
  obtain ⟨head,contents,cached,world⟩ := Queues.prev_peek_normal p.txQueue w t a e selected queue peekRun
  subst t
  obtain ⟨world,ambient,d',device',stored'⟩ := Origins.getPeer_return pid w s q e f readBack
  subst s
  subst f
  have sameDevice : d' = d := Option.some.inj (device'.symm.trans device)
  subst d'
  have samePeer : q = p := Option.some.inj (stored'.symm.trans stored)
  subst q
  cases finish
  have found : peerAt w pid = some p := by simp [peerAt,device,stored]
  obtain ⟨loans,named⟩ := account.peer_loans found
  obtain ⟨parts⟩ := peer_parts named
  have preserved := account.set_tx_queue found parts.txRun
    (by simpa only [contents] using parts.txRun) (List.Perm.refl _) e b setRun
  have afterWorld : v = replacePeer w d pid {p with txQueue := queue} := by
    have equality : replacePeer w d pid {p with txQueue := queue} = v ∧ e = b := by
      simpa [setPeer,modifyDev,replacePeer,device] using setRun
    exact equality.1.symm
  refine ⟨preserved,p,{p with txQueue := queue},found,?_,head,contents,cached⟩
  simp [peerAt,afterWorld,replacePeer]

end Leanux.Proofs.WG.RetirementSecurity
