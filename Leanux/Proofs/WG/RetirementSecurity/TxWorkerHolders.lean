import Leanux.Proofs.WG.RetirementSecurity.TxStoppedHolders
import Leanux.Proofs.WG.RetirementSecurity.TxRetirementFrames

/-! Native TX worker closure. Queue-head separation and peer-release funding
are concrete incoming caller facts. The worker obtains its key credit from
its actual cached batch, retains it through completion, and pays it once. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem txPeek_effect (pid : PeerId) (a b : Ambient)
    (run : ((txPeekSource pid).run w).run a = .ok ((first,v),b)) :
    ∃ d p queue, w.dev = some d ∧ d.peers[pid]? = some p ∧
      queue.all = p.txQueue.all ∧ queue.peeked = first ∧
      v = replacePeer w d pid {p with txQueue := queue} := by
  simp only [txPeekSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,pair,t,e,peekRun,q,s,f,readBack,_,r,g,setRun,finish⟩ := run
  obtain ⟨world,ambient,d,device,stored⟩ := Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  obtain ⟨selected,queue⟩ := pair
  obtain ⟨_,contents,cached,world⟩ := Queues.prev_peek_normal p.txQueue w t a e selected queue peekRun
  subst t
  obtain ⟨world,ambient,d',device',stored'⟩ := Origins.getPeer_return pid w s q e f readBack
  subst s
  subst f
  have sameDevice : d' = d := Option.some.inj (device'.symm.trans device)
  subst d'
  have samePeer : q = p := Option.some.inj (stored'.symm.trans stored)
  subst q
  cases finish
  have after : replacePeer w d pid {p with txQueue := queue} = v ∧ e = b := by
    simpa [setPeer,modifyDev,replacePeer,device] using setRun
  exact ⟨d,p,queue,device,stored,contents,cached,after.1.symm⟩

theorem PeerReleaseFunded.tx_queue (funded : PeerReleaseFunded pid w)
    (device : w.dev = some d) (found : d.peers[pid]? = some p) (queue : PrevQueue (List SkbId)) :
    PeerReleaseFunded pid (replacePeer w d pid {p with txQueue := queue}) := by
  intro q resident
  have same : q = {p with txQueue := queue} := by
    simpa [peerAt,replacePeer] using resident.symm
  subst q
  exact funded p (by simp [peerAt,device,found])

def txDropSource (pid : PeerId) : WG.M Unit := do
  setPeer pid {(← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked}

theorem txDrop_effect (pid : PeerId) (a b : Ambient)
    (run : ((txDropSource pid).run w).run a = .ok (((),v),b)) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧
      ((setPeer pid {p with txQueue := p.txQueue.dropPeeked}).run w).run a = .ok (((),v),b) ∧
      v = replacePeer w d pid {p with txQueue := p.txQueue.dropPeeked} := by
  simp only [txDropSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,q,s,f,readBack,setRun⟩ := run
  obtain ⟨world,ambient,d,device,stored⟩ := Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  obtain ⟨world,ambient,d',device',stored'⟩ := Origins.getPeer_return pid w s q a f readBack
  subst s
  subst f
  have sameDevice : d' = d := Option.some.inj (device'.symm.trans device)
  subst d'
  have samePeer : q = p := Option.some.inj (stored'.symm.trans stored)
  subst q
  have after : replacePeer w d pid {p with txQueue := p.txQueue.dropPeeked} = v ∧ a = b := by
    simpa [setPeer,modifyDev,replacePeer,device] using setRun
  exact ⟨d,p,device,stored,setRun,after.1.symm⟩

theorem TxSeparated.dropped (separated : TxSeparated pid w)
    (device : w.dev = some d) (found : d.peers[pid]? = some p)
    (peeked : p.txQueue.peeked = some items) :
    TxDetached items (replacePeer w d pid {p with txQueue := p.txQueue.dropPeeked}) := by
  have pfound : peerAt w pid = some p := by simp [peerAt,device,found]
  have selected : p.txQueue.all = items :: p.txQueue.dropPeeked.all := by
    simp [PrevQueue.all,PrevQueue.dropPeeked,peeked]
  intro other q qfound batch member head first
  by_cases same : pid = other
  · subst other
    have qeq : q = {p with txQueue := p.txQueue.dropPeeked} := by
      simpa [peerAt,replacePeer] using qfound.symm
    subst q
    exact separated p pfound items p.txQueue.dropPeeked.all selected pid p pfound
      batch (by simpa using member) head first
  · have oldFound : peerAt w other = some q := by
      simpa [peerAt,replacePeer,device,Std.TreeMap.getElem?_insert,same] using qfound
    exact separated p pfound items p.txQueue.dropPeeked.all selected other q oldFound
      batch (by simpa only [ite_eq_right same] using member) head first

theorem HolderAccount.drop_source (account : HolderAccount temporary w)
    (separated : TxSeparated pid w) (funded : PeerReleaseFunded pid w)
    (cached : ∀ p, peerAt w pid = some p → p.txQueue.peeked = some items)
    (a b : Ambient)
    (run : ((txDropSource pid).run w).run a = .ok (((),v),b)) :
    ∃ allocation, transmitLoan w pid items = some ⟨.transmit pid items,allocation⟩ ∧
      HolderAccount (allocation :: temporary) v ∧ TxDetached items v ∧ PeerReleaseFunded pid v := by
  obtain ⟨d,p,device,found,setRun,after⟩ := txDrop_effect pid a b run
  have pfound : peerAt w pid = some p := by simp [peerAt,device,found]
  obtain ⟨allocation,named,paid⟩ := account.drop_tx pfound (cached p pfound) a b setRun
  exact ⟨allocation,named,paid,after ▸ separated.dropped device found (cached p pfound),
    after ▸ funded.tx_queue device found p.txQueue.dropPeeked⟩

def txCompletionSource (pid : PeerId) (items : List SkbId) (head : DataPacket) : WG.M Unit := do
  if ← branch .txCrypted (head.state == .crypted) then createDataDone pid items

theorem completion_retirement (pid : PeerId) (items : List SkbId) (head : DataPacket)
    (temporary : Credits.Ledger) :
    Preserves (fun w => HolderAccount temporary w ∧ TxDetached items w ∧ PeerReleaseFunded pid w)
      (txCompletionSource pid items head) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  rw [txCompletionSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨crypted,u,c,check,tail⟩ := run
  have same : u = w := by cases check; rfl
  subst u
  cases crypted with
  | false => simp only [Bool.false_eq_true,ite_false] at tail; cases tail; exact before
  | true =>
    simp only [ite_true] at tail
    have fields := (ProjectedAction.iff_run_ambient _ _ _).mp
      (createDataDone_ownership pid items) w c () v b tail
    exact ⟨before.1.complete_tx pid items c b tail,before.2.1.points fields,
      before.2.2.complete pid items c b tail⟩

theorem txReadyTail_factor (pid : PeerId) (items : List SkbId) (headId : SkbId)
    (first : items.head? = some headId) :
    txReadyTail pid (some items) = (do
      let head ← getTxSkb headId
      txDropSource pid
      txCompletionSource pid items head
      Queues.TxDisposition.disposeSource pid items head.keypair) := by
  simp only [txReadyTail,first,txBeforeDispose,txDropSource,txCompletionSource,
    bind_assoc,Queues.RxCredits.bind_if_source,pure_bind]

theorem HolderAccount.ready_tail (account : HolderAccount temporary w)
    (separated : TxSeparated pid w) (funded : PeerReleaseFunded pid w)
    (cached : ∀ p, peerAt w pid = some p → p.txQueue.peeked = first)
    (a b : Ambient)
    (run : ((txReadyTail pid first).run w).run a = .ok ((result,v),b)) :
    result = true ∧ HolderAccount temporary v := by
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
      obtain ⟨allocation,named,after,detached,ready⟩ :=
        account.drop_source separated funded cached a e dropRun
      have namedKey : nameLoan w (.transmit pid items) head.keypair =
          some ⟨.transmit pid items,allocation⟩ := by
        simpa [transmitLoan,headId,device,stored] using named
      have key : allocation.slot = head.keypair := (nameLoan_resident namedKey).2.1
      rw [MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,completed,f,completeRun,disposeRun⟩ := tail
      have kept := (hoare_iff_run_ambient _ _ _).mp
        (completion_retirement pid items head (allocation :: temporary))
        dropped e () completed f ⟨after,detached,ready⟩ completeRun
      rw [← key] at disposeRun
      exact kept.1.dispose_tx kept.2.1 kept.2.2.ready f b disposeRun

theorem HolderAccount.tx_body (account : HolderAccount temporary w)
    (separated : TxSeparated pid w) (funded : PeerReleaseFunded pid w)
    (cached : ∀ p, peerAt w pid = some p → p.txQueue.peeked = first)
    (a b : Ambient)
    (run : ((Queues.TxDisposition.bodySource pid first).run w).run a = .ok ((result,v),b)) :
    HolderAccount temporary v := by
  rw [tx_body_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,testRun,tail⟩ := run
  have same := (hoare_iff_run_ambient _ _ _).mp (ready_world_frame first (fun s => s = w))
    w a ready u c rfl testRun
  subst u
  cases ready with
  | false => simp only [Bool.not_false,ite_true] at tail; cases tail; exact account
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    exact (account.ready_tail separated funded cached c b tail).2

theorem HolderAccount.tx_step (account : HolderAccount temporary w)
    (separated : TxSeparated pid w) (funded : PeerReleaseFunded pid w)
    (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((result,v),b)) : HolderAccount temporary v := by
  rw [txStep_peek_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨first,u,c,peek,body⟩ := run
  have kept := (account.peek_tx pid a c peek).1
  obtain ⟨d,p,queue,device,found,contents,cached,after⟩ := txPeek_effect pid a c peek
  have fields : peerOwnership {p with txQueue := queue} = peerOwnership p := by
    simp only [peerOwnership,slotFields,contents]
  have points : ownershipPointView u = ownershipPointView w :=
    after ▸ ownershipPoint_replace device found fields
  have ready : PeerReleaseFunded pid u := after ▸ funded.tx_queue device found queue
  have selected : ∀ q, peerAt u pid = some q → q.txQueue.peeked = first := by
    intro q resident
    have same : q = {p with txQueue := queue} := by
      simpa [peerAt,after,replacePeer] using resident.symm
    subst q
    exact cached
  exact kept.tx_body (separated.points points) ready selected c b body

end Leanux.Proofs.WG.RetirementSecurity
