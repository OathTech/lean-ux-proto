import TrustBase
import MemoryInvariant
import SystemInvariant

namespace Binary.RandomService
open TrustBase
local instance : Labels := Image.linkedLabels

structure Post (config : RandomProvider.Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (inputAt : DataMem → List Leanux.HiddenRecord → Prop) (s : MachineState) (ra : UInt64)
    (value : Nat) (rest : List Leanux.HiddenRecord) (t : MachineState) : Prop where
  returned : Returned s t ra
  frame : EqualOutside (RandomWrites config coverage preempt s) s.data.dmem t.data.dmem
  coverageState : AllowedipsCoverageAt coverage preempt t.data.dmem
  preemptState : load32 t.data.dmem preemptCountAddress=some preempt
  privateCheck : RandomProvider.check config coverage.task.toNat
    (RandomRecordingActive coverage preempt) t.data.dmem=.ok ()
  interrupts : t.data.system.bits[9]=s.data.system.bits[9]
  valueEqual : (t.data.regs.get (.low .rax .W32)).toNat=value
  remaining : inputAt t.data.dmem rest
  privilege : t.data.system.cpl=s.data.system.cpl
  direction : t.data.system.bits[10]=s.data.system.bits[10]
  mapped : ∀ a n, (s.data.dmem.loadInt a n).isSome=true → (t.data.dmem.loadInt a n).isSome=true

/-- Physical return and input agreement are applied independently. Actual
histories are extracted from the service's execution proof, never assumed
as a successful future insertion. CPL, DF and mappedness follow from the ISA. -/
theorem return_recorded (fetch : Int64 → Option Decoded) {config inputAt coverage preempt ra}
    (physical : RandomReturnContract fetch config)
    (coupling : RandomInputCoupling fetch config coverage preempt ra inputAt)
    {s records value rest}
    (entry : s.pc=.ofNat 0xffffffff81375200)
    (ready : RandomReady config coverage preempt s) (stack : EntryFrame s ra)
    (input : inputAt s.data.dmem records) (draw : Pair.Insert.draw records=.ok (value,rest)) :
    Eventually (instructionStep fetch) (Post config coverage preempt inputAt s ra value rest) s := by
  have run := physical coverage preempt s ra entry ready stack
  have actual := eventually_actual fetch s _ _ run .start (by simp)
  have ended := history_last fetch _ _ (by simp) actual
  have projected := history_project fetch _ _ ended
  have mode := SystemInvariant.eventually_mode fetch projected
  have mapped := MemoryInvariant.eventually_mapped fetch mode
  apply eventually_weaken (instructionStep fetch) _ _ _ _ mapped
  rintro t ⟨⟨⟨history,⟨⟨returned,frame,coverageState,preemptState,privateCheck,interrupts,noEntry⟩,actual⟩,last⟩,
    privilege,direction⟩,mapped⟩
  obtain ⟨valueEqual,remaining⟩ := coupling.returned s t history records value rest
    entry ready stack input draw actual last returned noEntry
  exact ⟨returned,frame,coverageState,preemptState,privateCheck,interrupts,valueEqual,
    remaining,privilege,direction,mapped⟩

#print axioms return_recorded

/-- View the returned heap with the same physical call-stack reservation.
This is a resource statement, not a claim that the caller has executed. -/
def entryView (s t : MachineState) : MachineState :=
  {t with data := {t.data with regs := {t.data.regs with rsp := s.data.regs.rsp}},pc := s.pc}

theorem Post.ready {config coverage preempt inputAt s ra value rest t}
    (post : Post config coverage preempt inputAt s ra value rest t)
    (ready : RandomReady config coverage preempt s) :
    RandomReady config coverage preempt (entryView s t) := by
  refine ⟨post.coverageState,post.preemptState,ready.capacity,post.privateCheck,
    post.privilege.trans ready.kernelMode,post.direction.trans ready.forward,?_,
    ready.privateApart,ready.stackApart,ready.bufferApart⟩
  intro i bound
  have mapped := post.mapped (s.data.regs.rsp.toBitVec-1024+.ofNat 64 i) 1
    ((loadInt_defined _ _ _).mpr (by
      intro j hj
      have zero : j=0 := by omega
      subst j
      simpa only [BitVec.add_zero] using ready.stackMapped i bound))
  have byte := (loadInt_defined _ _ _).mp mapped 0 (by decide)
  simpa only [entryView,BitVec.add_zero] using byte

#print axioms Post.ready
end Binary.RandomService
