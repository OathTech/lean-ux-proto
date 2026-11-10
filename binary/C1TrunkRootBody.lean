import C1TrunkCutExtra
import AllowedipsSourceModel
/-! Result C1, package 2: the empty root with the node installed, from the
landed boundary at +0x443 to `add`'s return, and the source side of the case
(`step` for case `root`, and its device as the landed `emptyInstalled`). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

theorem eax_zero (r t : Reg64s) (h : r.rax = .ofBitVec ((t.get (.low .rbx .W32)).setWidth 64))
    (zero : t.rbx = 0) : r.get (.low .rax .W32) = BitVec.ofInt 32 0 := by
  rw [low32_zext r _ h]
  simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, zero]
  decide

theorem step_root {d : Device} {family key cidr pid : Nat} {placed : Option NodeId} {exact : Bool}
    {outcomes : List Bool}
    (hc : (step d family key cidr pid placed exact outcomes).case = .root) :
    cidr ≤ (if family == 4 then 32 else 128) ∧
    (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = none ∧
    outcomes.head? = some true ∧
    step d family key cidr pid placed exact outcomes =
      ⟨.root,0,connect (addTail (alloc (bump d) (newNode key cidr (if family == 4 then 32 else 128)
        (some pid))) pid (bump d).nextNode) (if family == 4 then Slot.root4 else Slot.root6)
        (bump d).nextNode,1⟩ := by
  by_cases long : cidr > (if family == 4 then 32 else 128)
  · simp only [step, long, ↓reduceIte] at hc
    cases hc
  · have slot : slotOf (bump d) (if family == 4 then Slot.root4 else Slot.root6) =
        (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) := by
      by_cases four : (family == 4) = true <;> simp [four, slotOf, bump]
    unfold step at hc ⊢
    simp only [long, ↓reduceIte, slot] at hc ⊢
    cases root : (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) with
    | some rootId =>
      exfalso
      simp only [root] at hc
      repeat' split at hc
      all_goals first | cases hc | simp at hc
    | none =>
      simp only [root] at hc ⊢
      cases outcomes with
      | nil => cases hc
      | cons outcome rest =>
        cases outcome
        · cases hc
        · refine ⟨by omega,?_,?_,?_⟩ <;> first | trivial | rfl | simp

/-- `step`'s device for case `root` is the landed `emptyInstalled`. -/
theorem root_device (d0 : Device) (v4 : Bool) (key cidr pid : Nat) (owner : Peer)
    (hasPeer : d0.peers.get? pid = some owner) :
    connect (addTail (alloc d0 (newNode key cidr (if v4 then 32 else 128) (some pid))) pid d0.nextNode)
      (if v4 then Slot.root4 else Slot.root6) d0.nextNode =
      Model.emptyInstalled d0 v4 key cidr pid owner := by
  have hp : d0.peers[pid]? = some owner := by simpa using hasPeer
  cases v4 <;>
    simp [connect, addTail, alloc, setSlot, hp, Model.emptyInstalled, Model.rootWrite,
      Model.rootSlot, Model.rootWidth]

section
variable {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator} {c : Context}
  {s : MachineState} {w w' : World} {v4 : Bool} {key cidr pid : Nat} {ra : UInt64}
  {names : Allowedips.Names} {stream : List HiddenRecord} {d : Device} {seq : BitVec 64}
  {a : MachineData}

/-- Empty root, node installed: `add` from entry to return. -/
theorem root_body (below : NodeBelowTop) (alloc : AllocRule) (premises : Premises fetch L A)
    {family : Nat} (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (bound : cidr ≤ (if v4 then 32 else 128))
    (empty : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = none)
    (record : HiddenRecord) (rest : List HiddenRecord) (pending : stream = record :: rest)
    (recordSite : record.site = 77) (ok : record.bytes.head? = some 1)
    (after : ∃ d', w'.wg.dev = some d' ∧ ∀ owner, (bump d).peers.get? pid = some owner →
      Allowedips.target d' = Allowedips.target (Model.emptyInstalled (bump d) v4 key cidr pid owner))
    (recordsAfter : w'.ambient.hidden = some rest) (armedAfter : armed w' = true) :
    Eventually (instructionStep fetch) (AddPost L A c s w' v4 0 seq a) ⟨a,Add.entry⟩ := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have r := trunk.resources
  have tight := window_tight trunk.atAdd (insertWindow + A.depth) wide
  have heapOut := trunk.heapOutside
  apply eventually_trans (instructionStep fetch) _ _ _
    (root_allocated below alloc premises ready trunk bound empty record rest pending recordSite ok)
  rintro v ⟨n,at'⟩
  have checked := root_boundary (w := w) trunk bound empty at'
  obtain ⟨d0,owner,device0,hasPeer,run⟩ := Root.initialization_checked fetch premises.insertion checked
  have hd0 : d0 = bump d := (Option.some.inj device0).symm
  subst hd0
  apply eventually_trans (instructionStep fetch) _ _ _ run
  rintro t ⟨pcT,out,frameT,relatedT,shapeT⟩
  have v4eq : (v.data.regs.rbp.toNat == 32) = v4 := by
    rw [at'.bits]
    cases v4 <;> rfl
  rw [at'.rbx] at frameT relatedT shapeT
  rw [v4eq] at relatedT shapeT
  have spans := at'.object.writeSpans trunk v.data at'.rbx
  have covered : ∀ y, Root.Writes (names.allocated n) n
      (names.table+(if v.data.regs.rbp.toNat==32 then 0 else 8)) y →
      ∃ span ∈ Root.writeSpans (names.allocated n) v.data, span.contains y := by
    intro y written
    apply Root.writeSpans_cover (names.allocated n) v.data y
    rw [at'.rbx]
    rcases written with list | init | slot
    · exact .inr (.inl list)
    · exact .inl (range_mono _ 56 72 (by omega) y init)
    · have slot' : InRange (.ofNat 64 (names.table+(if v.data.regs.rbp.toNat = 32 then 0 else 8))) 8 y := by
        simpa only [beq_iff_eq] using slot
      exact .inr (.inr slot')
  have writesHeap (y : BitVec 64) (h : Root.Writes (names.allocated n) n
      (names.table+(if v.data.regs.rbp.toNat==32 then 0 else 8)) y) : L.Heap y := by
    obtain ⟨span,member,inside⟩ := covered y h
    exact (spans span member).2.1 y inside
  have spT : t.data.regs.rsp = a.regs.rsp - 96 := out.stack.trans at'.stack
  have word := call_word a v.data at'.stack
  have readyT : CallsReady c t.data := by
    refine ⟨?_,by rw [out.stack]; exact at'.ready.aligned,?_,
      by rw [out.stack]; exact at'.ready.pushSeparate,by rw [out.stack]; exact at'.ready.returnSeparate,
      at'.ready.metadataSeparate,at'.ready.preemptSeparate⟩
    · exact state_frame c v.data.dmem t.data.dmem at'.ready.state _ frameT
        (fun y read h => trunk.sep.heapBytes y (writesHeap y h) read)
    · rw [out.stack, ← frameT.loadInt _ 8 (fun i hi h => (heapOut _ (writesHeap _ h)).1 (by
        rw [word]
        exact window_sub a 0 8 (by decide) _ ⟨i,hi,by simp⟩))]
      exact at'.ready.mapped
  have loadT : ∀ off m : Nat, 8 ≤ off → off+m ≤ 112 →
      t.data.dmem.loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) m =
        (memory a 8).loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) m := by
    intro off m lo hi
    rw [← frameT.loadInt _ m (fun i hi' h =>
      (heapOut _ (writesHeap _ h)).1 (window_sub a off m hi _ ⟨i,hi',rfl⟩))]
    exact at'.loads off m lo hi
  have inArena' := at'.object.inArena trunk
  have projection : ∀ span ∈ readSpans (names.allocated n) Root.nodeOffsets, ∀ y, span.contains y →
      ¬Window a y ∧ ¬c.writes y := fun span member y inside =>
    heapOut y (read_heap (names := names.allocated n) trunk.table trunk.peers inArena' span member y inside)
  rw [Placement.at_pc t _ pcT]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (finish_tail fetch premises.insertion premises.tracePc r trunk.atAdd.returnWord readyT spT loadT
      relatedT shapeT projection)
  rintro f ⟨pcF,raxF,rspF,rbxF,rbpF,r12F,r13F,r14F,r15F,_,relatedF,shapeF,frameF⟩
  have seqHeap (i : Nat) (hi' : i < 8) :
      L.Heap (BitVec.ofNat 64 (L.table+AllowedipsMutationLayout.seq) + .ofNat 64 i) :=
    ⟨(L.table+AllowedipsMutationLayout.seq,8),by simp [Layout.heap, Layout.fixed, tableFields],⟨i,hi',rfl⟩⟩
  refine ⟨⟨pcF,rspF,rbxF,rbpF,r12F,r13F,r14F,r15F⟩,eax_zero _ _ raxF out.result,?_,?_,?_⟩
  · rw [← frameF.loadInt _ 8 (fun i hi' h =>
        h.elim (heapOut _ (seqHeap i hi')).1 (heapOut _ (seqHeap i hi')).2),
      ← frameT.loadInt _ 8 (fun i hi' h => by
        obtain ⟨span,member,inside⟩ := covered _ h
        exact (spans span member).2.2.1 _ inside ⟨i,hi',rfl⟩)]
    exact at'.seqWord
  · obtain ⟨d',device',same⟩ := after
    have live' : (names.allocated n).trie.nodes.map (·.2) = names.trie.nodes.map (·.2) ++ [n] := by
      simp [Names.allocated]
    refine ⟨names.allocated n,rest,trunk.table,trunk.peers,?_,armedAfter,recordsAfter,
      fun record' member => trunk.sites record' (pending ▸ List.mem_cons_of_mem _ member),
      trunk.objectsApart,inArena',?_⟩
    · apply assertAt_of_related device'
      · show Allowedips.reconstruct (names.allocated n) Root.nodeOffsets f.data.dmem =
          .ok (Allowedips.target d')
        rw [same owner hasPeer]
        exact relatedF
      · rw [same owner hasPeer]
        exact shapeF
    · rw [live']
      apply premises.allocator.frame v.data.dmem f.data.dmem _ _ at'.idle
      intro y arena notKept
      refine (frameT y (fun h => ?_)).trans (frameF y (fun h =>
        h.elim (heapOut y (arena_heap y arena)).1 (heapOut y (arena_heap y arena)).2))
      obtain ⟨span,member,inside⟩ := covered y h
      exact notKept ((spans span member).2.2.2 y inside arena)
  · intro y hy
    refine (at'.frame y hy).trans ((frameT y (fun h => hy (.inr (.inr (writesHeap y h))))).trans
      (frameF y (fun h => hy ?_)))
    rcases h with h | h
    · exact .inl (tight y h)
    · exact .inr (.inl h)
end

#print axioms step_root
#print axioms root_device
#print axioms root_body
end C1Trunk
