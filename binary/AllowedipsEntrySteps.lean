import AllowedipsEntryCallTrace
import AllowedipsEntryGuardTrace
import AllowedipsEntryQuery

namespace Binary.AllowedipsEntry
open TrustBase CommonBitsCoverage CommonBits Instrumentation
local instance : Labels := Image.linkedLabels

def AtPC (initial : MachineState) (coverage : KcovLayout) (old : BitVec 32)
    (ra : UInt64) (pc : Int64) (s : MachineState) : Prop :=
  s.pc=pc ∧ At initial coverage old ra s.data

def QueryAtPC (c : AllowedipsRelation.Config) (initial : MachineState)
    (coverage : KcovLayout) (old : BitVec 32) (ra : UInt64) (pc : Int64) (s : MachineState) : Prop :=
  s.pc=pc ∧ At initial coverage old ra s.data ∧
    AllowedipsChild.QueryWords s.data.dmem (slot initial 8) c.bits c.key

/-- Joining from an exact outer PC does not discard the actual history. -/
theorem chain_at (fetch : Int64 → Option Decoded)
    {initial coverage old ra start rx sig nextSig pc} {Q : MachineState → Prop}
    (first : Eventually (historyStep fetch) (fun t =>
      AtPC initial coverage old ra pc t.machine ∧ Local (Writes initial coverage old) start rx sig t)
      ⟨start,[start]⟩)
    (next : ∀ s, At initial coverage old ra s →
      Eventually (historyStep fetch) (fun t => Q t.machine ∧
        Local (Writes initial coverage old) ⟨s,pc⟩ rx nextSig t) ⟨⟨s,pc⟩,[⟨s,pc⟩]⟩) :
    Eventually (historyStep fetch) (fun t => Q t.machine ∧
      Local (Writes initial coverage old) start rx (sig++nextSig) t) ⟨start,[start]⟩ := by
  apply chain fetch _ start rx sig nextSig (AtPC initial coverage old ra pc) Q first
  rintro ⟨s,p⟩ ⟨equal,state⟩
  dsimp only at equal
  subst p
  exact next s state

theorem pc_call (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (contract : AllowedipsTracePcContract fetch)
    {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (offset : Nat) (site : offset ∈ [0x1b,0x47,0x61,0x14f,0x171])
    (s : MachineData) (state : At initial coverage old ra s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      AtPC initial coverage old ra (AllowedipsImage.Lookup.entry+.ofNat offset+5) t.machine ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+.ofNat offset⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+.ofNat offset⟩,[⟨s,AllowedipsImage.Lookup.entry+.ofNat offset⟩]⟩ := by
  have decoded : AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+.ofNat offset) =
      some ⟨callInstruction "L_ffffffff810f31f0",5⟩ := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at site
    rcases site with rfl | rfl | rfl | rfl | rfl <;> rfl
  have run := callback fetch _ "L_ffffffff810f31f0" (agree _ _ decoded) .pc contract pre s state rxSection
    (by
      intro after
      simp only [List.mem_cons,List.not_mem_nil,or_false] at site
      rcases site with rfl | rfl | rfl | rfl | rfl <;> rfl)
    (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at site
      rcases site with rfl | rfl | rfl | rfl | rfl <;> decide)
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  intro t h
  exact ⟨⟨h.1.1,h.1.2.1⟩,h.2⟩

theorem cmp_call (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (contract : AllowedipsTraceConstCmp1Contract fetch)
    {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (offset : Nat) (site : offset=0x39 ∨ offset=0x53)
    (s : MachineData) (state : At initial coverage old ra s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      AtPC initial coverage old ra (AllowedipsImage.Lookup.entry+.ofNat offset+5) t.machine ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+.ofNat offset⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+.ofNat offset⟩,[⟨s,AllowedipsImage.Lookup.entry+.ofNat offset⟩]⟩ := by
  have decoded : AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+.ofNat offset) =
      some ⟨callInstruction "L_ffffffff810f40c0",5⟩ := by rcases site with rfl | rfl <;> rfl
  have run := callback fetch _ "L_ffffffff810f40c0" (agree _ _ decoded) .constCmp1 contract pre s state rxSection
    (by intro after; rcases site with rfl | rfl <;> rfl)
    (by rcases site with rfl | rfl <;> decide)
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  intro t h
  exact ⟨⟨h.1.1,h.1.2.1⟩,h.2⟩

theorem arguments128 (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    {initial coverage old ra} (s : MachineData) (state : At initial coverage old ra s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      AtPC initial coverage old ra (AllowedipsImage.Lookup.entry+0x53) t.machine ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x4c⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x4c⟩,[⟨s,AllowedipsImage.Lookup.entry+0x4c⟩]⟩ := by
  apply eventually_weaken (historyStep fetch) _ _ _ _ (arguments128_trace fetch agree s rxSection)
  rintro t ⟨⟨regs,memory,pc⟩,trace⟩
  exact ⟨⟨pc,state.congr memory (by simp only [regs]) (by simp only [regs])
    (by simp only [regs]) (by simp only [regs])⟩,trace.mono (fun _ h => h.elim)⟩

theorem family32 (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    {c coverage old ra initial world v} (pre : AllowedipsEntry c coverage old ra initial world v)
    (s : MachineData) (state : At initial coverage old ra s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      AtPC initial coverage old ra
        (if c.bits=32 then AllowedipsImage.Lookup.entry+0x171 else AllowedipsImage.Lookup.entry+0x47) t.machine ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x3e⟩ rxSection
        [decisionView rxSection .swapEndian32 (c.bits==32)] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x3e⟩,[⟨s,AllowedipsImage.Lookup.entry+0x3e⟩]⟩ := by
  obtain ⟨_,_,physical⟩ := pre.related.2.1
  have family := physical.1.1
  have equal : (s.regs.get (.low .rbx .W8)==32)=(c.bits==32) := by
    rw [(state.family pre).1]
    rcases family with f | f <;> simp only [f] <;> rfl
  apply eventually_weaken (historyStep fetch) _ _ _ _
    (family32_trace fetch agree s (Writes initial coverage old) rxSection)
  rintro t ⟨⟨regs,memory,pc⟩,trace⟩
  refine ⟨⟨?_,state.congr memory (by rw [regs]) (by rw [regs]) (by rw [regs]) (by rw [regs])⟩,?_⟩
  · simpa only [equal,beq_iff_eq] using pc
  · simpa only [equal] using trace

theorem family128 (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    {c coverage old ra initial world v} (pre : AllowedipsEntry c coverage old ra initial world v)
    (family : c.bits=128) (s : MachineData) (state : At initial coverage old ra s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      AtPC initial coverage old ra (AllowedipsImage.Lookup.entry+0x14f) t.machine ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x58⟩ rxSection
        [decisionView rxSection .swapEndian128 true] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x58⟩,[⟨s,AllowedipsImage.Lookup.entry+0x58⟩]⟩ := by
  have equal : (s.regs.get (.low .rbx .W8)==128)=true := by
    rw [(state.family pre).1,family]; rfl
  apply eventually_weaken (historyStep fetch) _ _ _ _
    (family128_trace fetch agree s (Writes initial coverage old) rxSection)
  rintro t ⟨⟨regs,memory,pc⟩,trace⟩
  refine ⟨⟨?_,state.congr memory (by rw [regs]) (by rw [regs]) (by rw [regs]) (by rw [regs])⟩,?_⟩
  · simpa only [equal,↓reduceIte] using pc
  · simpa only [equal] using trace

#print axioms family32
#print axioms cmp_call
end Binary.AllowedipsEntry
