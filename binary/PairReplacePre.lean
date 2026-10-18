import PairReplace
import PairRemovePre
import PairReplaceOwnership

namespace Binary.Pair.Replace
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index

def Pre (n : Names) (o : Offsets) (c : Context) (s : MachineState)
    (w : World) (pid : PeerId) (kid : KeypairId) (ra : UInt64) : Prop :=
  callBoundary n o c s w pid kid ra=.ok ()

structure NewReady (o : Offsets) (m : DataMem) (d : Device) (kid : KeypairId) (base : Nat) : Prop where
  absent : d.indexTable.any (·.owner==.keypair kid)=false
  kind : word m "replace.new.kind" (base+o.kind) 4=.ok 2
  next : ∃ value, word m "replace.new.next" (base+o.hash+o.next) 8=.ok value
  index : ∃ value, word m "replace.new.index" (base+o.index) 4=.ok value

theorem pre_facts {n o c s w pid kid ra} (pre : Pre n o c s w pid kid ra) :
    ∃ d old new, w.k.wg=some d ∧ Corresponds n o s.data.dmem d ∧ storageCheck n o=true ∧
      Remove.ownership n o s.data.dmem=.ok (Remove.targetOwnership d) ∧
      (.handshake pid,old) ∈ n.owners ∧ (.keypair kid,new) ∈ n.owners ∧
      s.pc.toBitVec.toNat=entry ∧ s.data.regs.rsi.toNat=old ∧ s.data.regs.rdx.toNat=new ∧
      CallFacts n o c s ra 5 ∧
      (d.indexTable.any (·.owner==.handshake pid)=true → NewReady o s.data.dmem d kid new) := by
  unfold Pre callBoundary at pre
  obtain ⟨_,asserted,pre⟩ := bind_ok pre
  obtain ⟨d,device,related,storage,owned⟩ := remove_assert_ok asserted
  obtain ⟨old,oldAddress,pre⟩ := bind_ok pre
  obtain ⟨new,newAddress,pre⟩ := bind_ok pre
  obtain ⟨arguments,pre⟩ := check_ok _ _ _ _ pre
  have args : s.pc.toBitVec.toNat=entry ∧ s.data.regs.rsi.toNat=old ∧ s.data.regs.rdx.toNat=new := by
    simpa only [Bool.and_eq_true,beq_iff_eq,and_assoc] using arguments
  rw [device] at pre
  refine ⟨d,old,new,device,related,storage,owned,Remove.addressOf_ok oldAddress,
    Remove.addressOf_ok newAddress,args.1,args.2.1,args.2.2,?_⟩
  cases hashed : d.indexTable.any (·.owner==.handshake pid) with
  | false =>
    simp only [hashed,Bool.false_eq_true,↓reduceIte] at pre
    exact ⟨callFrameCheck_sound pre,by simp⟩
  | true =>
    simp only [hashed,↓reduceIte] at pre
    cases newHashed : d.indexTable.any (·.owner==.keypair kid) with
    | true => simp only [newHashed,↓reduceIte] at pre; cases pre
    | false =>
      simp only [newHashed,Bool.false_eq_true,↓reduceIte] at pre
      obtain ⟨kind,kindRead,pre⟩ := bind_ok pre
      obtain ⟨kindEq,pre⟩ := check_ok _ _ _ _ pre
      have kindEq : kind=2 := eq_of_beq kindEq
      subst kind
      obtain ⟨next,nextRead,pre⟩ := bind_ok pre
      obtain ⟨index,indexRead,pre⟩ := bind_ok pre
      exact ⟨callFrameCheck_sound pre,fun _ =>
        ⟨newHashed,mapError_ok kindRead,⟨next,mapError_ok nextRead⟩,⟨index,mapError_ok indexRead⟩⟩⟩

#print axioms pre_facts

theorem pre_of_parts {n o c s w pid kid ra d old new}
    (asserted : Remove.assertAt n o s.data.dmem w=.ok ())
    (oldAddress : addressOf n (.handshake pid)=.ok old)
    (newAddress : addressOf n (.keypair kid)=.ok new)
    (arguments : (s.pc.toBitVec.toNat==entry && s.data.regs.rsi.toNat==old && s.data.regs.rdx.toNat==new)=true)
    (device : w.k.wg=some d)
    (ready : d.indexTable.any (·.owner==.handshake pid)=true → NewReady o s.data.dmem d kid new)
    (frame : Index.callFrameCheck n o c s ra 5=.ok ()) : Pre n o c s w pid kid ra := by
  unfold Pre callBoundary
  rw [asserted,oldAddress,newAddress]
  apply check_of _ _ _ _ arguments
  rw [device]
  cases hashed : d.indexTable.any (·.owner==.handshake pid) with
  | false =>
    simp only [hashed,Bool.false_eq_true,↓reduceIte]
    exact frame
  | true =>
    have fields := ready hashed
    obtain ⟨next,nextRead⟩ := fields.next
    obtain ⟨index,indexRead⟩ := fields.index
    simp only [hashed,fields.absent,Bool.false_eq_true,↓reduceIte,fields.kind,nextRead,indexRead]
    exact frame

end Binary.Pair.Replace
