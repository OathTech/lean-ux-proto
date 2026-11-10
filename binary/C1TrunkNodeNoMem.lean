import C1TrunkPlus
/-! Result C1, package 2: the common finish through `Exits` (`finish_exit`,
after package 3's `exit_post`), and the path on which the allocation at :205
is refused (`-ENOMEM`, nothing changed but the sequence word). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

theorem ebx_nomem (r : Reg64s) (h : r.rbx = 0xfffffff4) :
    r.get (.low .rbx .W32) = BitVec.ofInt 32 (-ENOMEM) := by
  simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, h, ENOMEM]
  decide

theorem ebx_zero (r : Reg64s) (h : r.rbx = 0) : r.get (.low .rbx .W32) = BitVec.ofInt 32 0 := by
  simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, h]
  decide

section
variable {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator} {c : Context}
  {s : MachineState} {w w' : World} {v4 : Bool} {key cidr pid : Nat} {ra : UInt64}
  {names : Allowedips.Names} {stream : List HiddenRecord} {d : Device} {seq : BitVec 64}
  {a : MachineData}

/-- From the common exit `x` of `add` to `InsertPost`, through the `Exits`
clause of an earlier state `e` of `add`'s frame. -/
theorem finish_exit {e x : MachineState} {answer : Int} (exits : Exits fetch L A c s ra e)
    (pcX : x.pc = Add.entry + 0x549) (spX : x.data.regs.rsp = e.data.regs.rsp)
    (flightX : InFlight L A c s x) (readyX : CallsReady c x.data)
    (keptX : ∀ y, InRange (e.data.regs.rsp.toBitVec + 48)
        (s.data.regs.rsp.toNat + 8 - (e.data.regs.rsp.toNat + 48)) y →
      x.data.dmem.get? y = e.data.dmem.get? y)
    (result : x.data.regs.get (.low .rbx .W32) = BitVec.ofInt 32 answer)
    (seqX : SeqAdvanced L s x) (invX : Inv L A w' x.data.dmem) :
    Eventually (instructionStep fetch) (InsertPost L A c s w' ra answer) x := by
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (exits x pcX spX flightX readyX keptX)
  rintro t ⟨returned,eax,outside,heap,invT⟩
  refine ⟨returned,eax.trans result,?_,invT w' invX,?_⟩
  · obtain ⟨before,atEntry,atX⟩ := seqX
    refine ⟨before,atEntry,?_⟩
    rw [← readNat_frame (before := x) (after := t) (writes := fun y => ¬L.Heap y)
      (fun y hy => (heap y (Classical.not_not.mp hy)).symm) _ 8
      (fun y inside => not_not_intro ⟨(L.table+AllowedipsMutationLayout.seq,8),
        by simp [Layout.heap, Layout.fixed, tableFields],inside⟩)]
    exact atX
  · intro y unwritten
    exact (flightX.frame y unwritten).trans
      (outside y (fun h => unwritten (h.elim .inl (fun h => .inr (.inl h)))))

/-- Nonempty root, no exact match, the service returns NULL: `add` from its
entry to the insertion's return. -/
theorem nodeNoMem_body (framed : FramedHolds) (alloc : AllocRule) (premises : Premises fetch L A)
    {family : Nat} (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (bound : cidr ≤ (if v4 then 32 else 128)) (keyBound : key < 2^(if v4 then 32 else 128))
    (rootId : NodeId)
    (rootAt : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some rootId)
    (rootNode : ∃ node, (bump d).nodes.get? rootId = some node ∧ node.bitlen = (if v4 then 32 else 128))
    (placed : Option NodeId)
    (ambient finalAmbient : Ambient) (finalStore : AipStore)
    (accepted : ((WG.nodePlacement (some rootId) key cidr (if v4 then 32 else 128)).run
      (Source.Aip.store (bump d))).run ambient = .ok (((placed,false),finalStore),finalAmbient))
    (record : HiddenRecord) (rest : List HiddenRecord) (pending : stream = record :: rest)
    (recordSite : record.site = 78) (failed : record.bytes.head? = some 0)
    (after : ∃ d', w'.wg.dev = some d' ∧ Allowedips.target d' = Allowedips.target (bump d))
    (recordsAfter : w'.ambient.hidden = some rest) (armedAfter : armed w' = true) :
    Eventually (instructionStep fetch) (InsertPost L A c s w' ra (-ENOMEM)) ⟨a,Add.entry⟩ := by
  apply eventually_trans (instructionStep fetch) _ _ _
    (trunk_walked premises trunk bound keyBound rootId rootAt rootNode placed false
      ambient finalAmbient finalStore accepted)
  intro t walked
  obtain ⟨bpT,r14T⟩ := walked.open' rfl
  apply eventually_trans (instructionStep fetch) _ _ _ (node_reach premises trunk walked)
  rintro e ⟨u,at',bx,bp,r14,r15⟩
  apply eventually_trans (instructionStep fetch) _ _ _
    (node_called (bits := if v4 then 32 else 128) alloc premises ready trunk at' (bx.trans walked.rbx)
      (by rw [bp]; exact bpT) (r14.trans r14T) (by rw [r15]; exact walked.r15) record rest pending
      recordSite)
  rintro b ⟨t1,result,mid,pcB,_,heapB⟩
  have outcome : t1.data.regs.rax.toNat = 0 ∧
      A.Idle t1.data.dmem (names.trie.nodes.map (·.2)) rest := result.1 failed
  have null : t1.data.regs.rax.toBitVec = 0 := BitVec.eq_of_toNat_eq outcome.1
  rw [ite_eq_left null] at pcB
  rw [Placement.at_pc b _ pcB]
  have run := SystemInvariant.eventually_mode fetch
    (region_eventually (Add_r692_layout.agreement premises.insertion.add) b.data _ (nomem_code b.data))
  apply eventually_trans (instructionStep fetch) _ _ _ run
  rintro x ⟨⟨regsX,memX,pcX⟩,_,forwardX⟩
  have spX : x.data.regs.rsp = b.data.regs.rsp := by rw [regsX]
  have flightB := mid.flight trunk (Add.entry+0x692)
  have flightX : InFlight L A c s x :=
    ⟨by rw [spX]; exact flightB.low,by rw [spX]; exact flightB.high,by rw [memX]; exact flightB.frame,
      by rw [memX]; exact flightB.mapped,forwardX.trans mid.forward,by rw [memX]; exact mid.ready.state⟩
  refine finish_exit (mid.exits framed premises trunk (Add.entry+0x692)) pcX spX flightX
    (mid.ready.congr memX spX) (fun y _ => by rw [memX]) (ebx_nomem _ (by rw [regsX])) ?_ ?_
  · obtain ⟨before,atEntry,atB⟩ := mid.seqAdvanced trunk (Add.entry+0x692)
    exact ⟨before,atEntry,by simpa only [readNat, memX] using atB⟩
  · obtain ⟨d',device',same⟩ := after
    refine ⟨names,rest,trunk.table,trunk.peers,?_,armedAfter,recordsAfter,
      fun record' member => trunk.sites record' (pending ▸ List.mem_cons_of_mem _ member),
      trunk.objectsApart,trunk.inArena,?_⟩
    · apply assertAt_of_related device'
      · show Allowedips.reconstruct names Root.nodeOffsets x.data.dmem = .ok (Allowedips.target d')
        rw [same, memX]
        exact mid.related
      · rw [same, memX]
        exact mid.shape
    · apply premises.allocator.frame t1.data.dmem x.data.dmem _ _ outcome.2
      intro y arena _
      rw [memX]
      exact (heapB y (arena_heap y arena)).symm
end

#print axioms finish_exit
#print axioms nodeNoMem_body
end C1Trunk
