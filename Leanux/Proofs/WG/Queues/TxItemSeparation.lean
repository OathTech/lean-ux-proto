import Leanux.Proofs.WG.Queues.TxMarkTransport
import Leanux.Proofs.WG.Queues.PassiveHolders

/-! Actual staged TX allocation uses the shared TX/RX nextSkb frontier.
The returned item is fresh relative to every initially resident packet.
These are native source cuts, without an executable replacement observer. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.ItemSeparation
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Std.Do

/-- The exact native allocator returns consecutive IDs in source order,
retains the device epoch and Ambient state, and leaves older cells intact. -/
theorem allocate_result (packets : List DataPacket) {w v : WGWorld} {d : Device}
    {a b : Ambient} {item : List SkbId} (device : w.dev=some d)
    (run : ((packets.mapM newTxSkb).run w).run a=.ok ((item,v),b)) :
    item=List.range' d.nextSkb packets.length ∧ b=a ∧
      ∃ e,v.dev=some e ∧ e.nextSkb=d.nextSkb+packets.length ∧ e.ifindex=d.ifindex ∧
        ∀ target,target<d.nextSkb→txPackets v target=txPackets w target := by
  induction packets generalizing w v d a b item with
  | nil=>
    simp only [List.mapM_nil] at run
    cases run
    exact ⟨rfl,rfl,d,device,by simp,rfl,fun _ _=>rfl⟩
  | cons packet packets ih=>
    simp only [List.mapM_cons,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨id,u,clock,head,tail⟩ := run
    rw [Packets.newTxSkb_run w a d packet device] at head
    cases head
    obtain ⟨ids,last,lastClock,rest,finish⟩ := tail
    cases finish
    let next := {d with txSkbs:=d.txSkbs.insert d.nextSkb packet,nextSkb:=d.nextSkb+1}
    have hd : (Packets.update w (fun v=>{v with txSkbs:=v.txSkbs.insert d.nextSkb packet, nextSkb:=d.nextSkb+1})).dev=some next := by simp [Packets.update,device,next]
    obtain ⟨idsEq,ambientEq,e,atEnd,frontier,epoch,kept⟩ := ih hd rest
    refine ⟨?_,ambientEq,e,atEnd,?_,epoch,?_⟩
    · simp only [idsEq,List.length_cons,List.range'_succ,next]
    · simpa [next,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using frontier
    · intro target below
      rw [kept target (Nat.lt_trans below (Nat.lt_succ_self d.nextSkb))]
      simp [txPackets,Packets.update,device,Std.TreeMap.getElem?_insert,
        (Nat.ne_of_lt below).symm]

/-- Existing packet boundedness turns actual residency into a strict bound
below the next allocation ID. No freshness field is added to the source. -/
theorem resident_below (bounded : Packets.Inv w) (device : w.dev=some d)
    (resident : txPackets w target=some packet) : target<d.nextSkb := by
  have bound := bounded (.inl target) (target+1)
  have present : (Packets.snapshot w).slots (.inl target)=some (target+1) := by
    simpa [Packets.snapshot,Packets.deviceStore,txPackets,device] using
      congrArg (Option.map fun _=>target+1) resident
  have := bound present
  have bound' : target+1≤d.nextSkb := by simpa only [Packets.snapshot,device,Packets.deviceStore] using this
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self target) bound'

variable {w v : WGWorld} {d : Device} {a b : Ambient}
  {item old : List SkbId} {packets : List DataPacket}

theorem allocate_nodup (device : w.dev=some d)
    (run : ((packets.mapM newTxSkb).run w).run a=.ok ((item,v),b)) : item.Nodup := by
  rw [(allocate_result packets device run).1]
  exact List.nodup_range'

/-- Freshness of the returned source item is derived for every old resident
cell; an item-disjointness premise is unnecessary at this allocation cut. -/
theorem allocate_resident (bounded : Packets.Inv w)
    (resident : txPackets w target=some packet)
    (run : ((packets.mapM newTxSkb).run w).run a=.ok ((item,v),b)) :
    target∉item ∧ txPackets v target=some packet := by
  cases device:w.dev with
  | none=>simp [txPackets,device] at resident
  | some d=>
    have below := resident_below bounded device resident
    obtain ⟨ids,_,e,_,_,_,kept⟩ := allocate_result packets device run
    refine ⟨?_,(kept target below).trans resident⟩
    rw [ids]
    intro member
    obtain ⟨i,_,eq⟩ := List.mem_range'.mp member
    have lower : d.nextSkb≤target := by simpa only [eq,Nat.one_mul] using Nat.le_add_right d.nextSkb i
    exact (Nat.not_le_of_gt below) lower

/-- An actual old item whose cells are resident is disjoint from the newly
allocated item. Residency is explicit; queue membership alone does not imply it. -/
theorem allocate_disjoint (bounded : Packets.Inv w)
    (resident : ∀ target∈old,∃packet,txPackets w target=some packet)
    (run : ((packets.mapM newTxSkb).run w).run a=.ok ((item,v),b)) :
    ∀target∈old,target∉item := by
  intro target oldMember
  obtain ⟨packet,cell⟩ := resident target oldMember
  exact (allocate_resident bounded cell run).1

/-- The exact allocation-and-create suffix of staged send preserves a saved
head without assuming disjointness of its future allocated item. -/
theorem allocate_create_head (pid : PeerId) (packets : List DataPacket)
    (target : SkbId) (state : PacketState) :
    Hoare (do let item←packets.mapM newTxSkb;createData pid item)
      (fun w=>Packets.Inv w ∧ HeadState target state w) (fun _=>HeadState target state) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  obtain ⟨item,u,clock,allocated,created⟩ := RxCredits.bind_ok_native run
  obtain ⟨packet,resident,mark⟩ := hi.2
  obtain ⟨outside,kept⟩ := allocate_resident hi.1 resident allocated
  exact (hoare_iff_run_ambient _ _ _).mp (MarkTransport.create_head target pid item outside state)
    u clock result v b ⟨packet,kept,mark⟩ created

/-- Source-acquired sending references do not alter the packet allocation
frontier or packet cells. This uses the exact existing acquisition receipt. -/
theorem acquire_head (kid : KeypairId) (target : SkbId) (state : PacketState) :
    Preserves (fun w=>Packets.Inv w ∧ HeadState target state w) (Affiliation.sendAcquire kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  obtain ⟨_,_,_,_,_,_,_,_,_,borrowed⟩ := Affiliation.sendAcquire_certificate kid w v a b run
  obtain ⟨d,p,device,_,_,same⟩ := borrowed
  have newDevice := congrArg WGStoreView.dev same
  change v.dev=some {d with peers:=d.peers.insert _ {p with refcount:=p.refcount+1}} at newDevice
  have oldDevice : w.dev=some d := device
  refine ⟨?_,?_⟩
  · simpa only [Packets.Inv,Packets.snapshot,oldDevice,newDevice,Packets.deviceStore] using hi.1
  · simpa only [HeadState,txPackets,oldDevice,newDevice,Option.bind_some] using hi.2

/-- The literal original staged-submit source acquires, allocates and calls
createData. Normal refusal cleanup is included, without any input credit,
key-affiliation, disjoint-item or output-state premise. -/
theorem staged_submit_head (pid kid : Nat) (packets : List DataPacket)
    (target : SkbId) (state : PacketState) :
    Hoare (RxCredits.stagedSubmit pid kid packets)
      (fun w=>Packets.Inv w ∧ HeadState target state w) (fun _=>HeadState target state) := by
  unfold RxCredits.stagedSubmit
  exact hoare_bind _ _ (acquire_head kid target state)
    (fun _=>allocate_create_head pid packets target state)

/-- The same concrete staged-submit run retains the existing holder account
and saved head while absorbing exactly its attributed TX/send delta. The
key-owner compatibility is the existing staging handoff input, not output funding. -/
theorem staged_submit_account {holders : RxCredits.DurableHolders}
    (pid kid : Nat) (packets : List DataPacket) (target : SkbId) (state : PacketState)
    (funded : holders.Funded cs loans w) (bounded : Packets.Inv w)
    (head : HeadState target state w) (compatible : RxCredits.KeyCompatible pid kid w)
    (run : ((RxCredits.stagedSubmit pid kid packets).run w).run a=.ok (((),v),b)) :
    ∃ delta,RxCredits.Handoff w v [] [] delta ∧
      (holders.absorb delta).Funded cs loans v ∧ HeadState target state v := by
  obtain ⟨delta,step⟩ := RxCredits.stagedSubmit_handoff packets compatible a b run
  have effects := (RxCredits.KeyEffects.iff_run_ambient _ _).mp
    (RxCredits.stagedSubmit_keyEffect (allowed:=RxCredits.NoPromotion) pid kid packets) w a () v b run
  have keys : RxCredits.KeysCompatible v :=
    ⟨effects.rxCompatible step.rx funded.carriers.keys.1,
      effects.currentsCompatible funded.carriers.keys.2 (fun _ _ h=>h.elim)⟩
  have passive := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.PassiveHolders.«0».Leanux.Proofs.WG.Queues.RxCredits.PassiveHolders.submit_preserves)
      pid kid packets (RxCredits.DurableHolders.passiveView w)) w a () v b rfl run
  have initial : holders.Funded cs (loans++[]) w := by simpa only [List.append_nil] using funded
  have after := initial.handoff step keys passive
  refine ⟨delta,step,?_,?_⟩
  · simpa only [List.append_nil] using after
  · exact (hoare_iff_run_ambient _ _ _).mp (staged_submit_head pid kid packets target state)
      w a () v b ⟨bounded,head⟩ run

end Leanux.Proofs.WG.Queues.TxDisposition.ItemSeparation
