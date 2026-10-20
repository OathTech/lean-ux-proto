import AllowedipsPlacementSaved
import AllowedipsPlacementLoop

namespace Binary.Pair.Allowedips.Placement
open Leanux Leanux.WG TrustBase CommonBitsCoverage AllowedipsMutationImage AllowedipsRelation
local instance : Labels := Image.linkedLabels

def ptr (nodes : Nat → BitVec 64) (id : Option NodeId) : UInt64 := .ofBitVec (pointer nodes id)

/-- Accumulators are related only at the header and the two exits. A NULL
child is parked at the real empty-tail code until the source's next iteration. -/
def Position (nodes : Nat → BitVec 64) (store : AipStore) (root : Option NodeId) (bits key : Nat) (peer : BitVec 64) (acc : Acc) (s : MachineState) : Prop :=
  match acc.1 with
  | some (parent,exact) => s.pc=(if exact then Add.entry+0x3ca else Add.entry+0x120) ∧
      s.data.regs.rbx=ptr nodes parent ∧
      (exact=false → s.data.regs.rbp=.ofBitVec ((BitVec.ofNat 32 bits).setWidth 64) ∧ s.data.regs.r14=.ofBitVec peer)
  | none => s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8=some ((ptr nodes acc.2.2).toNat : Int) ∧
      match acc.2.1 with
      | none => s.pc=Add.entry+0x55f ∧ s.data.regs.rbx=ptr nodes acc.2.2
      | some id => s.pc=Add.entry+0xf7 ∧ s.data.regs.rbx=.ofBitVec (nodes id) ∧
          Reached (fun id => store.nodes.get? id) root bits key id

/-- Physical read facts for nodes in the component store. The checked-entry
bridge derives these from reconstruction and the executable separation checks. -/
structure Inputs (base : MachineData) (c : Context) (nodes : Nat → BitVec 64)
    (store : AipStore) (root : Option NodeId) (key cidr bits : Nat) (peer : BitVec 64) : Prop where
  saved : SavedInput base c (.ofNat 32 bits) peer
  node : ∀ id node, Reached (fun id => store.nodes.get? id) root bits key id → store.nodes.get? id=some node →
    NodeInput base c (.ofBitVec (nodes id)) bits key cidr node
  child : ∀ id node next, Reached (fun id => store.nodes.get? id) root bits key id → store.nodes.get? id=some node →
    node.cidr≤AllowedipsRelation.common bits node.bits key → node.cidr<bits →
    node.bit[childIndex node key]?=some next →
    ChildInput base c (.ofBitVec (nodes id)) bits key node.cidr (pointer nodes next) ∧
      ∀ nid, next=some nid → nodes nid≠0

theorem Inputs.step (fetch : Int64 → Option Decoded) (decoder : AllowedipsDecoderAgreement fetch)
    (mutation : AllowedipsMutationDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch) (cmp : AllowedipsTraceCmp1Contract fetch)
    {base c nodes store root key cidr bits peer} (inputs : Inputs base c nodes store root key cidr bits peer)
    (acc : Acc) (next : ForInStep Acc) (machine : MachineState)
    (selected : selectStep store key cidr bits acc=some next) (openLoop : acc.1=none)
    (frame : Frame base c machine.data) (position : Position nodes store root bits key peer acc machine) :
    Eventually (instructionStep fetch) (fun t => Frame base c t.data ∧
      Position nodes store root bits key peer (match next with | .done a => a | .yield a => a) t) machine := by
  rcases acc with ⟨answer,current,parent⟩
  change answer=none at openLoop
  subst answer
  cases current with
  | none =>
    have eq : .done (some (parent,false),none,parent)=next := Option.some.inj selected
    subst next
    obtain ⟨_,pc,cursor⟩ := position
    have first := inputs.saved.empty_exit fetch mutation frame
    rw [at_pc machine _ pc]
    apply eventually_weaken (instructionStep fetch) _ _ _ _ first
    rintro t ⟨pc,frame,bp,r14,bx⟩
    exact ⟨frame,pc,bx.trans cursor,fun _ => ⟨bp,r14⟩⟩
  | some id =>
    obtain ⟨parentRead,pc,cursor,reached⟩ := position
    have saved : machine.data.dmem.loadInt base.regs.rsp.toBitVec 8=some ((ptr nodes parent).toNat : Int) := by
      simpa only [frame.stack] using parentRead
    cases present : store.nodes[id]? with
    | none => simp [selectStep,present] at selected
    | some node =>
      have input := inputs.node id node reached present
      have first := input.prefix fetch decoder mutation callbacks cmp frame cursor
      rw [at_pc machine _ pc]
      apply eventually_trans (instructionStep fetch) _ _ _ first
      rintro t1 ⟨pc1,frame1,bx1,bp1,parent1⟩
      by_cases matched : node.cidr≤cidr ∧ node.cidr≤AllowedipsRelation.common bits node.bits key
      · have selection := selected
        simp [selectStep,present,Nat.not_lt.mpr matched.1,Nat.not_lt.mpr matched.2] at selection
        rw [ite_eq_left matched] at pc1
        have second := input.exact_segment fetch mutation callbacks.pc cmp frame1 bx1 bp1
        rw [at_pc t1 _ pc1]
        apply eventually_trans (instructionStep fetch) _ _ _ second
        rintro t2 ⟨pc2,frame2,bx2,_,parent2⟩
        by_cases exactLength : node.cidr=cidr
        · have eq : next=.done (some (some id,true),some id,some id) := by
            simpa only [ite_eq_left exactLength,Option.some.injEq] using selection.symm
          subst next
          exact .done _ ⟨frame2,by simpa only [Position,ite_eq_left exactLength,ite_true] using pc2,bx2,by intro h; cases h⟩
        · rw [ite_eq_right exactLength] at pc2
          by_cases invalid : node.cidr≥node.bitlen
          · simp [exactLength,invalid] at selection
          · cases child : node.bit[childIndex node key]? with
            | none =>
              simp only [childIndex] at child
              simp [exactLength,invalid,child] at selection
            | some nextId =>
              have eq : next=.yield (none,nextId,some id) := by
                have child' := child
                simp only [childIndex] at child'
                simpa [exactLength,invalid,child'] using selection.symm
              subst next
              obtain ⟨data,nonnull⟩ := inputs.child id node nextId reached present matched.2
                (by have := input.cidrBound; omega) child
              have third := data.segment fetch mutation callbacks.pc frame2 bx2 (by
                rw [parent2,parent1,saved]; rfl)
              rw [at_pc t2 _ pc2]
              apply eventually_weaken (instructionStep fetch) _ _ _ _ third
              rintro t3 ⟨pc3,frame3,bx3,parent3⟩
              refine ⟨frame3,?_,?_⟩
              · simpa only [frame3.stack,ptr,pointer,Option.map_some,Option.getD_some,UInt64.toNat_toBitVec,
                  UInt64.toBitVec_ofBitVec] using parent3
              · cases nextId with
                | none => exact ⟨by simpa [pointer] using pc3,by simpa [ptr,pointer] using bx3⟩
                | some nextId =>
                  have notNull := nonnull nextId rfl
                  have notNull' : nodes nextId≠0#64 := notNull
                  exact ⟨by simpa [pointer,notNull'] using pc3,by simpa [pointer,notNull'] using bx3,
                    .child id node nextId reached present matched.2 data.short child⟩
      · rw [ite_eq_right matched] at pc1
        have eq : next=.done (some (parent,false),some id,parent) := by
          by_cases short : node.cidr≤cidr
          · have different : ¬node.cidr≤AllowedipsRelation.common bits node.bits key := fun h => matched ⟨short,h⟩
            simpa [selectStep,present,Nat.not_lt.mpr short,Nat.lt_of_not_ge different] using selected.symm
          · simpa [selectStep,present,Nat.lt_of_not_ge short] using selected.symm
        subst next
        have second := inputs.saved.restore fetch mutation frame1 (pointer nodes parent)
          (by change _=some ((pointer nodes parent).toNat : Int)
              simpa [ptr] using parent1.trans saved)
        rw [at_pc t1 _ pc1]
        apply eventually_weaken (instructionStep fetch) _ _ _ _ second
        rintro t2 ⟨pc2,frame2,bp2,r14,bx2⟩
        exact ⟨frame2,pc2,bx2,fun _ => ⟨bp2,r14⟩⟩

#print axioms Inputs.step
end Binary.Pair.Allowedips.Placement
