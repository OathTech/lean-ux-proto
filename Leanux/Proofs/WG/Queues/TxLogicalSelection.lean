import Leanux.Proofs.WG.Queues.TxItemSeparation
import Leanux.Proofs.WG.Queues.TxSelectedEncrypt

/-! Logical live ring items, rather than stale occupied slots, identify the
actual encryption selection. Fresh allocation separates a refused head from
every live item whose IDs are below the actual allocation frontier. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LogicalSelection
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

/-- The selected normal consume is precisely the live logical head, even
when consumed items remain physically present pending batch retirement. -/
theorem consumed_live {r next : PtrRing α} (physical : Ring.Source.Refines (PtrRing.init n) h r)
    (consumed : r.consume=(some item,next)) : r.items=item::next.items := by
  have old := physical.initialized.2.1
  have after := (physical.step .poll).initialized.2.1
  simp only [Ring.Journal.step,consumed] at after
  simp only [Ring.Journal.admitted,Ring.Journal.consumed,List.filterMap_append,
    List.filterMap_cons,List.filterMap_nil,List.append_nil] at after old
  rw [old,List.append_assoc] at after
  exact List.append_cancel_left after

/-- Actual allocator freshness separates every newly returned ID from old
logical live items. Only their numeric frontier bound is needed: physical
slot occupancy and packet residency are deliberately not assumed. -/
theorem allocated_outside {r : PtrRing (List SkbId)} {packets : List DataPacket}
    {item : List SkbId} {w v : WGWorld} {a b : Ambient} (device : w.dev=some d)
    (bounded : ∀old∈r.items,∀id∈old,id<d.nextSkb)
    (run : ((packets.mapM newTxSkb).run w).run a=.ok ((item,v),b)) :
    ∀id∈item,∀old∈r.items,id∉old := by
  have ids := (ItemSeparation.allocate_result packets device run).1
  intro id fresh old live member
  have upper := bounded old live id member
  rw [ids] at fresh
  obtain ⟨i,_,same⟩ := List.mem_range'.mp fresh
  have lower : d.nextSkb≤id := by
    simpa only [same,Nat.one_mul] using Nat.le_add_right d.nextSkb i
  exact (Nat.not_le_of_gt upper) lower

private theorem allocation_context (packets : List DataPacket) :
    SameView (fun w : WGWorld=>w.dev.map fun d=>(d.peers,d.ifindex,d.encryptQueue))
      (packets.mapM newTxSkb) := by
  intro initial
  apply mapM_view_spec id (fun w : WGWorld=>
    (w.dev.map fun d=>(d.peers,d.ifindex,d.encryptQueue))=initial)
  intro packet
  unfold newTxSkb
  apply hoare_liftSkb
  intro w d store hi hd
  simpa only [id_eq,hd,Option.map_some] using hi

/-- The actual fresh allocation/create source returns a DEAD refused head,
retains the entry encrypt ring, and derives exclusion from its old live items.
Only live-item frontier bounds are required; stale slots are unrestricted. -/
theorem allocated_refusal (pid : PeerId) (packets : List DataPacket)
    (device : w.dev=some d)
    (peer : d.peers[pid]?=some p) (live : p.isDead=false)
    (room : p.txQueue.count<MAX_QUEUED_PACKETS) (full : d.encryptQueue.full=true)
    (bounded : ∀old∈d.encryptQueue.items,∀id∈old,id<d.nextSkb)
    (run : (((do let item←packets.mapM newTxSkb;createData pid item;pure item) : WG.M (List SkbId)).run w).run a=
      .ok ((first::rest,v),b)) :
    txQueues v pid=some (p.txQueue.enqueue (first::rest)) ∧ HeadState first .dead v ∧
      TxRing.nativeCell v=some (d.ifindex,d.encryptQueue) ∧
      ∀old∈d.encryptQueue.items,first∉old := by
  obtain ⟨item,u,clock,allocated,tail⟩ := RxCredits.bind_ok_native run
  obtain ⟨value,last,lastClock,created,finish⟩ := RxCredits.bind_ok_native tail
  cases finish
  have apart := allocated_outside device bounded allocated first (by simp)
  have context := (ProjectedAction.iff_run_ambient _ _ _).mp (allocation_context packets)
    w a (first::rest) u clock allocated
  obtain ⟨e,atEnd,_,_,_⟩ := (ItemSeparation.allocate_result packets device allocated).2.2
  have fields : (e.peers,e.ifindex,e.encryptQueue)=(d.peers,d.ifindex,d.encryptQueue) := by
    simpa only [atEnd,device,Option.map_some,Option.some.injEq] using context
  have peers : e.peers=d.peers := congrArg Prod.fst fields
  have epoch : e.ifindex=d.ifindex := congrArg (fun x=>x.2.1) fields
  have ring : e.encryptQueue=d.encryptQueue := congrArg (fun x=>x.2.2) fields
  have endpoint := (hoare_iff_run_ambient _ _ _).mp
    (create_pipe pid first rest e p (by simpa only [peers] using peer) live room
      (by simpa only [ring] using full)) u clock value v b atEnd created
  exact ⟨endpoint.1,endpoint.2.1,by simpa only [epoch,ring] using endpoint.2.2,apart⟩

/-- The literal native ring poll selects from its input logical live list;
its output state is the actual consumed ring, not a later callback endpoint. -/
theorem selected_outside (cell : TxRing.nativeCell w=some (epoch,r))
    (physical : TxRing.Refines (PtrRing.init n) h r)
    (outside : ∀old∈r.items,target∉old)
    (run : (TxRing.pollSource.run w).run a=.ok ((some item,v),b)) : target∉item := by
  have result := (TxRing.poll_result cell run).1
  have consumed : r.consume=(some item,r.consume.2) := Prod.ext result.symm rfl
  have live := consumed_live physical consumed
  apply outside item
  rw [live]
  exact List.mem_cons_self

private theorem poll_packets : SameView txPackets TxRing.pollSource := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases hd:w.dev with
  | none=>
    simp [TxRing.pollSource,getDev,hd,invariant,AmbientM.invariant] at run
    cases run
  | some d=>
    simp [TxRing.pollSource,getDev,hd,modifyDev] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    funext id
    simp only [txPackets,hd,Option.bind_some]

/-- A fresh EPIPE-refused item is excluded from the next actually selected
old live item. The selected item is saved before any softirq callback. -/
theorem refusal_then_selection (pid : PeerId) (packets : List DataPacket)
    (device : w.dev=some d)
    (peer : d.peers[pid]?=some p) (live : p.isDead=false)
    (room : p.txQueue.count<MAX_QUEUED_PACKETS) (full : d.encryptQueue.full=true)
    (bounded : ∀old∈d.encryptQueue.items,∀id∈old,id<d.nextSkb)
    (physical : TxRing.Refines (PtrRing.init n) h d.encryptQueue)
    (created : (((do let item←packets.mapM newTxSkb;createData pid item;pure item) : WG.M (List SkbId)).run w).run a=
      .ok ((first::rest,u),middle))
    (polled : (TxRing.pollSource.run u).run middle=.ok ((some selected,v),b)) :
    HeadState first .dead v ∧ first∉selected := by
  obtain ⟨_,head,ring,apart⟩ := allocated_refusal pid packets device peer live room full bounded created
  refine ⟨?_,selected_outside ring physical apart polled⟩
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp poll_packets u middle (some selected) v b polled
  simpa only [HeadState,same] using head

end Leanux.Proofs.WG.Queues.TxDisposition.LogicalSelection
