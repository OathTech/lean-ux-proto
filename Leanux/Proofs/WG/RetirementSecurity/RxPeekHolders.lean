import Leanux.Proofs.WG.RetirementSecurity.RxCleanupHolders
import Leanux.Proofs.WG.RetirementSecurity.RxHolderTransfer
import Leanux.Proofs.WG.Queues.RxPollCarrier

/-! Actual RX cached-peek and dequeue transport the key-reference account.
The cache does not add a reference; the native two-getter drop moves exactly
its selected key occurrence to the poll local. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG

theorem HolderAccount.peek_rx (account : HolderAccount temporary w) (pid : PeerId)
    (a b : Ambient)
    (run : ((Queues.peekRxQueue pid).run w).run a = .ok ((first,v),b)) :
    HolderAccount temporary v ∧ ∃ before after,
      peerAt w pid = some before ∧ peerAt v pid = some after ∧
      first = before.rxQueue.all.head? ∧ after.rxQueue.all = before.rxQueue.all ∧
      after.rxQueue.peeked = first := by
  simp only [Queues.peekRxQueue,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,pair,t,e,peekRun,q,s,f,readBack,_,r,g,setRun,finish⟩ := run
  obtain ⟨world,ambient,d,device,stored⟩ := Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  obtain ⟨selected,queue⟩ := pair
  obtain ⟨head,contents,cached,world⟩ := Queues.prev_peek_normal p.rxQueue w t a e selected queue peekRun
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
  have preserved := account.set_rx_queue found parts.rxRun
    (by simpa only [contents] using parts.rxRun) (List.Perm.refl _) e b setRun
  have afterWorld : v = replacePeer w d pid {p with rxQueue := queue} := by
    have equality : replacePeer w d pid {p with rxQueue := queue} = v ∧ e = b := by
      simpa [setPeer,modifyDev,replacePeer,device] using setRun
    exact equality.1.symm
  refine ⟨preserved,p,{p with rxQueue := queue},found,?_,head,contents,cached⟩
  simp [peerAt,afterWorld,replacePeer]

theorem HolderAccount.drop_rx_native {id : SkbId} (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) (peeked : p.rxQueue.peeked = some id)
    (a b : Ambient)
    (run : ((Queues.dropRxQueue pid).run w).run a = .ok (((),v),b)) :
    ∃ allocation, receiveLoan w pid id = some ⟨.receive pid id,allocation⟩ ∧
      HolderAccount (allocation :: temporary) v := by
  unfold Queues.dropRxQueue at run
  rw [Queues.getPeer_twice] at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨read,u,c,readRun,setRun⟩ := run
  obtain ⟨world,clock,d,device,resident⟩ := Origins.getPeer_return pid w u read a c readRun
  subst u
  subst c
  have equality : read = p := Option.some.inj
    ((show peerAt w pid = some read by simp [peerAt,device,resident]).symm.trans found)
  subst read
  exact account.drop_rx found peeked a b setRun

/-- Actual RX carrier uniqueness and exact queued multiplicities imply that
an already selected occurrence is absent from every physical peer RX queue. -/
theorem selected_rx_detached {id : SkbId}
    (inventory : Queues.RxCredits.Inventory (selected :: rest) w)
    (queues : Queues.RxCredits.QueueOwners (selected :: rest) w)
    (phase : selected.phase = .selected) (device : w.dev = some d)
    (packet : selected.packet = ⟨d.ifindex,id⟩) : RxDetached id w := by
  intro pid p found member
  have peer : d.peers[pid]? = some p := by simpa [peerAt,device] using found
  have count := queues d pid p id device peer
  have positive : 0 < p.rxQueue.all.count id := List.count_pos_iff.mpr member
  rw [count] at positive
  obtain ⟨other,inside⟩ := List.exists_mem_of_length_pos positive
  obtain ⟨inside,pred⟩ := List.mem_filter.mp inside
  have same : other.packet = selected.packet := by
    have field : other.packet = ⟨d.ifindex,id⟩ := by
      simp only [Bool.and_eq_true,beq_iff_eq] at pred
      exact pred.1.1
    exact field.trans packet.symm
  rcases List.mem_cons.mp inside with equal | later
  · subst other
    simp [phase] at pred
  · have absent := (List.nodup_cons.mp inventory.distinct).1
    exact absent (List.mem_map.mpr ⟨other,later,same⟩)

/-- Native dequeue transfers the actual selected RX key occurrence and
establishes detachment from campaign 1's physical carrier ledger. A numeric
key account alone is not used to infer packet uniqueness. -/
theorem HolderAccount.drop_rx_carrier {id : SkbId} (account : HolderAccount temporary w)
    (carriers : Queues.RxCredits.CarrierState entries loans w)
    (device : w.dev = some d) (peer : d.peers[pid]? = some p)
    (peeked : p.rxQueue.peeked = some id) (a b : Ambient)
    (run : ((Queues.dropRxQueue pid).run w).run a = .ok (((),v),b)) :
    ∃ allocation, receiveLoan w pid id = some ⟨.receive pid id,allocation⟩ ∧
      HolderAccount (allocation :: temporary) v ∧
      Queues.RxCredits.CarrierState
        (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.selected⟩ ::
          Queues.RxCredits.remaining entries [⟨d.ifindex,id⟩]) loans v ∧ RxDetached id v := by
  obtain ⟨allocation,loan,keys⟩ := account.drop_rx_native
    (by simp [peerAt,device,peer]) peeked a b run
  have after := Queues.RxCredits.drop_state carriers device peer peeked a b run
  have endpoint : v = {w with dev := some {d with peers := d.peers.insert pid {p with rxQueue := p.rxQueue.dropPeeked}}} := by
    have done := run
    simp [Queues.dropRxQueue,getPeer,getDev,setPeer,modifyDev,device,peer] at done
    exact done.1.symm
  refine ⟨allocation,loan,keys,after,?_⟩
  exact selected_rx_detached (d := {d with peers := d.peers.insert pid {p with rxQueue := p.rxQueue.dropPeeked}})
    after.inventory after.queues rfl (by rw [endpoint]) rfl

end Leanux.Proofs.WG.RetirementSecurity
