import Leanux.Proofs.WG.RetirementSecurity.TxCreateHolders
import Leanux.Proofs.WG.RetirementSecurity.TxAllocationHolders

/-! The actual staged submission suffix acquires its peer, allocates the
packet list and enters createData. Packet separation and nonfinal peer
release are derived here from native operations. The saved key occurrence,
packet allocation bound and key-to-peer affiliation remain visible inputs. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem allocate_first_packet (packet : DataPacket) (packets : List DataPacket)
    (device : w.dev = some d) (a b : Ambient)
    (run : (((packet :: packets).mapM newTxSkb).run w).run a = .ok ((items,v),b)) :
    items.head? = some d.nextSkb ∧ Queues.TxDisposition.txPackets v d.nextSkb = some packet := by
  simp only [List.mapM_cons,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨first,u,c,headRun,rest,t,e,tailRun,finish⟩ := run
  rw [Packets.newTxSkb_run w a d packet device] at headRun
  cases headRun
  cases finish
  let next := {d with txSkbs := d.txSkbs.insert d.nextSkb packet,nextSkb := d.nextSkb + 1}
  have nextDevice : (Packets.update w (fun current => {current with
      txSkbs := current.txSkbs.insert d.nextSkb packet,nextSkb := d.nextSkb + 1})).dev = some next := by
    simp [Packets.update,device,next]
  have kept := (Queues.TxDisposition.ItemSeparation.allocate_result packets nextDevice tailRun).2.2
  obtain ⟨_,_,_,_,kept⟩ := kept
  refine ⟨rfl,?_⟩
  rw [kept d.nextSkb (by simp [next])]
  simp [Queues.TxDisposition.txPackets,Packets.update,device]

theorem HolderAccount.saved_key (account : HolderAccount (allocation :: temporary) w) :
    ∃ k, keyAt w allocation.slot = some k ∧ k.internalId = allocation.stamp := by
  obtain ⟨loans,_,credits⟩ := account
  obtain ⟨k,resident,stamp,_⟩ := credits.resident
    (allocation := allocation) (by simp)
  exact ⟨k,resident,stamp⟩

theorem HolderAccount.staged_submit (account : HolderAccount (allocation :: temporary) w)
    (bounded : Packets.Inv w) (compatible : Queues.RxCredits.KeyCompatible pid allocation.slot w)
    (packet : DataPacket) (packets : List DataPacket) (key : packet.keypair = allocation.slot)
    (a b : Ambient)
    (run : ((do
      Affiliation.sendAcquire allocation.slot
      let items ← (packet :: packets).mapM newTxSkb
      createData pid items).run w).run a = .ok (((),v),b)) : HolderAccount temporary v := by
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,acquireRun,items,t,e,allocateRun,createRun⟩ := run
  obtain ⟨d,k,actual,p,device,resident,word,stored,positive,borrow⟩ :=
    Affiliation.sendAcquire_certificate allocation.slot w u a c acquireRun
  have owner : actual = pid := by
    simpa [Affiliation.Compatible,word] using compatible d k device resident
  subst actual
  obtain ⟨d',p',device',stored',_,current⟩ := borrow
  have sameDevice : d' = d := Option.some.inj (device'.symm.trans device)
  subst d'
  have samePeer : p' = p := Option.some.inj (stored'.symm.trans stored)
  subst p'
  have after : u.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} :=
    congrArg WGStoreView.dev current
  have hu : HolderAccount (allocation :: temporary) u := by
    apply (account.peer_fields device stored
      (q := {p with refcount := p.refcount + 1}) ⟨rfl,rfl,rfl⟩).store
    simp [holderStore,Origins.view,peersAt,packetKeyWords,replacePeer,after]
  have boundedU : Packets.Inv u := by
    simpa [Packets.Inv,Packets.snapshot,Packets.deviceStore,after,device] using bounded
  have readyU : PeerReleaseReady pid u := by
    intro q found final
    simp [peerAt,after] at found
    subst q
    simp only at final
    omega
  obtain ⟨ht,detached⟩ := hu.allocate_tx boundedU (packet :: packets) c e allocateRun
  have perimeter := (ProjectedAction.iff_run_ambient _ _ _).mp
    (allocate_perimeter (packet :: packets)) u c items t e allocateRun
  have readyT := readyU.peers (congrArg (fun shape => shape.2.1) perimeter)
  obtain ⟨head,cell⟩ := allocate_first_packet packet packets after c e allocateRun
  obtain ⟨currentKey,currentResident,stamp⟩ := ht.saved_key
  have batch : transmitLoan t pid items = some ⟨.transmit pid items,allocation⟩ := by
    have named : nameLoan t (.transmit pid items) allocation.slot =
        some ⟨.transmit pid items,allocation⟩ := by
      cases allocation
      simp [nameLoan,currentResident,stamp]
    simpa [transmitLoan,head,key,
      show t.dev.bind (fun dev => dev.txSkbs[d.nextSkb]?) = some packet from cell] using named
  exact ht.create_tx batch detached readyT e b createRun

end Leanux.Proofs.WG.RetirementSecurity
