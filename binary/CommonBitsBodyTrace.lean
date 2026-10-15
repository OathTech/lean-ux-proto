import CommonBitsQuiet
import CommonBitsGuardTrace
import CommonBitsCallbackTrace
import CommonBitsBodySteps

namespace Binary.CommonBits
open TrustBase Instrumentation
local instance : Labels := Image.linkedLabels

theorem pure_body_trace (fetch : Int64 → Option Decoded)
    (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData) (state : BodyAt i c s)
    (start finish : Int64) (registers : Reg64s) (rxSection : Nat) (signature : List EventView)
    (stack : registers.rsp = s.regs.rsp) (node : registers.r12 = s.regs.r12)
    (key : registers.r13 = s.regs.r13) (r14 : registers.r14 = s.regs.r14)
    (r15 : registers.r15 = s.regs.r15)
    (run : Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = registers ∧ t.machine.data.dmem = s.dmem ∧ t.machine.pc = finish) ∧
      Local (i.Writes c) ⟨s,start⟩ rxSection signature t) ⟨⟨s,start⟩,[⟨s,start⟩]⟩) :
    Eventually (historyStep fetch) (fun t =>
      BodyStep i c s finish registers.rbx registers.rbp t.machine ∧
      Local (i.Writes c) ⟨s,start⟩ rxSection signature t) ⟨⟨s,start⟩,[⟨s,start⟩]⟩ := by
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨⟨regs,memory,pc⟩,trace⟩
  refine ⟨⟨pc, ?_, by simp only [regs], by simp only [regs], ?_, ?_, trace.frame⟩,trace⟩
  · exact state.same_memory memory (by simpa only [regs] using stack)
      (by simpa only [regs] using node) (by simpa only [regs] using key)
  · simpa only [regs] using r14
  · simpa only [regs] using r15

theorem callback_body_trace (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (here : fetch pc = some ⟨callInstruction target,5⟩) (kind : KcovKind)
    (contract : AllowedipsServiceReturns fetch (label target)
      (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat)
    (silent : ∀ after, AllowedipsObservation.edge rxSection ⟨s,pc⟩ after = .ok [])
    (ordinary : pc ≠ Image.PeerGet.entry+0xaf ∧ pc ≠ Image.PeerGet.entry+0x4a) :
    Eventually (historyStep fetch) (fun t =>
      BodyStep i c s (pc+5) s.regs.rbx s.regs.rbp t.machine ∧
      Local (i.Writes c) ⟨s,pc⟩ rxSection [] t) ⟨⟨s,pc⟩,[⟨s,pc⟩]⟩ := by
  have run := callback_trace fetch pc target here kind contract c s state.ready rxSection silent ordinary
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨⟨returned,ready⟩,trace⟩
  obtain ⟨atPC,sp,bx,bp,r12,r13,r14,r15⟩ := returned_caller s (pc+5) (label target) t.machine returned
  have trace' : Local (i.Writes c) ⟨s,pc⟩ rxSection [] t := by
    change Local (fun a => InRange (i.stack.toBitVec-8) 8 a ∨ c.writes a) _ _ _ _
    simpa only [state.stack] using trace
  exact ⟨⟨atPC,state.after_callback apart ready sp r12 r13 trace.frame,bx,bp,r14,r15,trace'.frame⟩,trace'⟩

/-- Compose two body fragments while preserving both actual path segments. -/
theorem body_chain (fetch : Int64 → Option Decoded)
    (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData)
    (start middle finish : Int64) (bx bp endBx endBp : UInt64) (rxSection : Nat)
    (firstSignature secondSignature : List EventView)
    (first : Eventually (historyStep fetch) (fun t =>
      BodyStep i c s middle bx bp t.machine ∧
      Local (i.Writes c) ⟨s,start⟩ rxSection firstSignature t) ⟨⟨s,start⟩,[⟨s,start⟩]⟩)
    (next : ∀ t : MachineData, BodyAt i c t → t.regs.rbx = bx → t.regs.rbp = bp →
      Eventually (historyStep fetch) (fun u => BodyStep i c t finish endBx endBp u.machine ∧
        Local (i.Writes c) ⟨t,middle⟩ rxSection secondSignature u)
        ⟨⟨t,middle⟩,[⟨t,middle⟩]⟩) :
    Eventually (historyStep fetch) (fun t => BodyStep i c s finish endBx endBp t.machine ∧
      Local (i.Writes c) ⟨s,start⟩ rxSection (firstSignature++secondSignature) t)
      ⟨⟨s,start⟩,[⟨s,start⟩]⟩ := by
  apply chain fetch (i.Writes c) ⟨s,start⟩ rxSection firstSignature secondSignature
    (BodyStep i c s middle bx bp) (BodyStep i c s finish endBx endBp) first
  intro t post
  have run := next t.data post.body post.rbx post.rbp
  have eq : (⟨t.data,middle⟩ : MachineState) = t := by cases t; congr 1; exact post.atPC.symm
  rw [eq] at run
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro u ⟨step,trace⟩
  refine ⟨⟨step.atPC,step.body,step.rbx,step.rbp,step.r14.trans post.r14,
    step.r15.trans post.r15,?_⟩,trace⟩
  intro a outside
  exact (post.frame a outside).trans (step.frame a outside)

/-- A proved silent argument/arithmetic prefix, followed by the real callback. -/
theorem prefix_callback_history (fetch : Int64 → Option Decoded)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (start callPC : Int64)
    (registers : Reg64s) (rxSection : Nat) (target : Label) (kind : KcovKind)
    (contract : AllowedipsServiceReturns fetch (label target)
      (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (here : fetch callPC = some ⟨callInstruction target,5⟩)
    (stack : registers.rsp = s.regs.rsp) (node : registers.r12 = s.regs.r12)
    (key : registers.r13 = s.regs.r13) (r14 : registers.r14 = s.regs.r14)
    (r15 : registers.r15 = s.regs.r15)
    (silent : ∀ data after, AllowedipsObservation.edge rxSection ⟨data,callPC⟩ after = .ok [])
    (ordinary : callPC ≠ Image.PeerGet.entry+0xaf ∧ callPC ≠ Image.PeerGet.entry+0x4a)
    (prefixRun : Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = registers ∧ t.machine.data.dmem = s.dmem ∧ t.machine.pc = callPC) ∧
      Local (i.Writes c) ⟨s,start⟩ rxSection [] t) ⟨⟨s,start⟩,[⟨s,start⟩]⟩) :
    Eventually (historyStep fetch) (fun t =>
      BodyStep i c s (callPC+5) registers.rbx registers.rbp t.machine ∧
      Local (i.Writes c) ⟨s,start⟩ rxSection [] t) ⟨⟨s,start⟩,[⟨s,start⟩]⟩ := by
  apply body_chain fetch i c s start callPC (callPC+5) registers.rbx registers.rbp
    registers.rbx registers.rbp rxSection [] []
    (pure_body_trace fetch i c s state start callPC registers rxSection [] stack node key r14 r15 prefixRun)
  intro t ht bx bp
  have executed := callback_body_trace fetch callPC target here kind contract i c apart t ht rxSection
    (silent t) ordinary
  apply eventually_weaken (historyStep fetch) _ _ _ _ executed
  rintro u ⟨step,trace⟩
  exact ⟨⟨step.atPC,step.body,step.rbx.trans bx,step.rbp.trans bp,step.r14,step.r15,step.frame⟩,trace⟩

end Binary.CommonBits
