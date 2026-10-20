import PairCallSource
import PairCountFrame
import PairPeerEffect
import AllowedipsSelected
import AllowedipsTailReady

namespace Binary.Pair.Trie
open Leanux Leanux.WG TrustBase CommonBitsCoverage
local instance : Labels := Image.linkedLabels

theorem loopWrites_middle {cfg coverage old ra initial entry} {v : AllowedipsRelation.View}
    (post : AllowedipsEntry.Post cfg initial coverage old ra entry) {a : BitVec 64}
    (written : AllowedipsLoop.writes entry.data.regs.rsp ⟨coverage,old+512⟩ a) :
    AllowedipsTail.MiddleWrites cfg v initial coverage old a := by
  rcases written with scratch | buffer
  · left
    have coordinate : entry.data.regs.rsp.toBitVec-48=initial.data.regs.rsp.toBitVec-144+16 := by
      rw [post.stack,UInt64.toBitVec_sub,BitVec.sub_sub]
      change initial.data.regs.rsp.toBitVec-128=initial.data.regs.rsp.toBitVec-(128+16)+16
      rw [←BitVec.sub_sub,BitVec.sub_add_cancel]
    rw [coordinate] at scratch
    exact range_shift_inside _ 16 48 64 (by decide) scratch
  · exact .inr (.inl buffer)

structure MiddlePost (names : Names) (o : AllowedipsProbe.Offsets) (d : Device)
    (cfg : AllowedipsRelation.Config) (v : AllowedipsRelation.View) (coverage : Context)
    (initial entry : MachineState) (answer : Option PeerId) (state : MachineState) : Prop where
  pc : state.pc=AllowedipsImage.Lookup.entry+0x122
  result : state.data.regs.rax.toBitVec=AllowedipsRelation.pointer (interpretation names.peers) answer
  related : Corresponds names o state.data.dmem d
  stack : state.data.regs.rsp=initial.data.regs.rsp-80
  active : (Context.mk coverage.coverage (coverage.preempt+512)).At state.data.dmem
  mapped : (state.data.dmem.loadInt (state.data.regs.rsp.toBitVec-8) 8).isSome=true
  frame : EqualOutside (AllowedipsTail.MiddleWrites cfg v initial coverage.coverage coverage.preempt)
    entry.data.dmem state.data.dmem

theorem selected_segment (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsDecoderAgreement fetch) (pc : AllowedipsTracePcContract fetch)
    {base state : MachineState} {coverage : Context} (atCut : state.pc=AllowedipsImage.Lookup.entry+0x101)
    (frame : AllowedipsLoop.Frame base.data coverage state.data) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs.rbp=state.data.regs.rbp ∧
      t.pc=(if state.data.regs.rbp.toBitVec==0 then AllowedipsImage.Lookup.entry+0x184 else AllowedipsImage.Lookup.entry+0x110) ∧
      AllowedipsLoop.Frame base.data coverage t.data) state := by
  have run := AllowedipsOuter.selected_start fetch decoder pc base.data state.data coverage frame 0 [state] [] rfl
    (by rw [←atCut]; rfl)
  have start : (⟨state.data,AllowedipsImage.Lookup.entry+0x101⟩ : MachineState)=state := by rw [←atCut]
  rw [←start]
  apply Sequential.forget run
  rintro t ⟨bp,position,_,trace⟩
  refine ⟨bp,?_,trace.frame⟩
  simpa only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,
    Width.bits,Nat.sub_zero,BitVec.extractLsb'_eq_self] using position

theorem miss_segment (fetch : Int64 → Option Decoded) (decoder : AllowedipsDecoderAgreement fetch)
    {names o d cfg v coverage initial entry state ra}
    (post : AllowedipsEntry.Post cfg initial coverage.coverage coverage.preempt ra entry)
    (atCut : state.pc=AllowedipsImage.Lookup.entry+0x184)
    (frame : AllowedipsLoop.Frame entry.data ⟨coverage.coverage,coverage.preempt+512⟩ state.data)
    (related : Corresponds names o state.data.dmem d) :
    Eventually (instructionStep fetch)
      (MiddlePost names o d cfg v coverage initial entry none) state := by
  have run := region_eventually (AllowedipsLookup.r184_layout.agreement decoder) state.data _ (Allowedips.noMatch state.data)
  have start : (⟨state.data,AllowedipsImage.Lookup.entry+0x184⟩ : MachineState)=state := by rw [←atCut]
  rw [←start]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨regs,memory,position⟩
  refine ⟨position,by rw [regs]; rfl,by rw [memory]; exact related,
    by rw [regs]; exact frame.stack.trans post.stack,
    by rw [memory]; exact frame.ready.state,?_,?_⟩
  · rw [regs,memory]
    exact frame.ready.mapped
  · rw [memory]
    intro a outside
    exact frame.memory a (fun written => outside (loopWrites_middle post written))

/-- The executed tail preserves reconstructed data and exports callback
state for the next call, as well as ABI restoration and the returned peer. -/
theorem finish_segment (fetch : Int64 → Option Decoded) (decoder : AllowedipsDecoderAgreement fetch)
    (pc : AllowedipsTracePcContract fetch) (bh : AllowedipsBhEnableContract fetch)
    {names} {input : AllowedipsProbe.Input} {coverage initial entry state w d root bits key ra d' answer}
    (pre : AllowedipsEntry (callConfig names w d root bits key) coverage.coverage coverage.preempt ra initial w
      (callView (callConfig names w d root bits key) d))
    (facts : CallFacts names input.offsets coverage initial ra bits key)
    (post : AllowedipsEntry.Post (callConfig names w d root bits key) initial coverage.coverage coverage.preempt ra entry)
    (middle : MiddlePost names input.offsets d' (callConfig names w d root bits key)
      (callView (callConfig names w d root bits key) d) coverage initial entry answer state) :
    Eventually (instructionStep fetch) (fun t =>
      AllowedipsTail.Post initial coverage.coverage coverage.preempt ra
        (.ofBitVec (AllowedipsRelation.pointer (interpretation names.peers) answer)) t ∧
      Corresponds names input.offsets t.data.dmem d' ∧
      EqualOutside (fun a => AllowedipsEntry.TotalWrites initial coverage.coverage coverage.preempt a ∨
        AllowedipsCountWrites (callConfig names w d root bits key)
          (callView (callConfig names w d root bits key) d) a) entry.data.dmem t.data.dmem) state := by
  have ready := AllowedipsTail.Ready.of_middle_frame pre post middle.stack middle.active middle.mapped middle.frame
  have run := AllowedipsTail.execution fetch decoder pc bh pre state.data ready 0
  have start : (⟨state.data,AllowedipsImage.Lookup.entry+0x122⟩ : MachineState)=state := by rw [←middle.pc]
  rw [←start]
  have apart := spansApart_disjoint facts.decoderApart
    (show Covers (decoderSpans names input.offsets) (ReadBytes names input.offsets) from fun _ read => decoderSpans_cover read)
    (callTotalWrites_cover initial coverage)
  apply Sequential.forget run
  rintro t ⟨returned,path⟩
  have result : state.data.regs.rax=UInt64.ofBitVec (AllowedipsRelation.pointer (interpretation names.peers) answer) :=
    UInt64.toBitVec_inj.mp middle.result
  refine ⟨result ▸ returned,(reconstruct_frame names input.offsets path.frame
    (fun a read write => apart a read (AllowedipsTail.writes_total write))).symm.trans middle.related,?_⟩
  intro a outside
  apply (middle.frame a ?_).trans (path.frame a (fun write => outside (.inl (AllowedipsTail.writes_total write))))
  rintro (scratch | buffer | count)
  · obtain ⟨i,hi,equal⟩ := scratch
    exact outside (.inl (.inl ⟨i,by omega,equal⟩))
  · exact outside (.inl (.inr (.inl ⟨.inr buffer.1,buffer.2⟩)))
  · exact outside (.inr count)

#print axioms miss_segment
#print axioms finish_segment
end Binary.Pair.Trie
