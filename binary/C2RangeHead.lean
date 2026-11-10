import C2RangeSteps
import CanonicalLoads
import KcovInvariant

/-! Work package 2 of result C2: the head of the range (+0 to +161, call sites 1 to 7):
the load of the packet counter, the add to the preempt count, the two limit rejections,
the spill of the incremented counter, the too-old rejection, the spill of its word index
and the in-window branch. -/
namespace Binary.C2
open Binary TrustBase
local instance : Labels := Binary.Image.linkedLabels

section
variable {layout : KcovLayout} {preempt : BitVec 32} {s0 : MachineState} {kp skb nonce : BitVec 64}

/-- The add to the preempt count: the coverage state for the raised count. The metadata
and the buffer are apart from the count's four bytes (`Context.coverageApart`). -/
theorem preempt_raised (ctx : Context layout preempt s0 kp skb nonce) :
    KcovState layout (preempt + 0x200)
      (s0.data.dmem.storeInt preemptCountAddress 4 (0x200 + preempt).toInt) := by
  have frame := storeInt_frame s0.data.dmem preemptCountAddress 4 (0x200 + preempt).toInt
  obtain ⟨metadata, _, buffer⟩ := ctx.coverage
  have field (base : BitVec 64) (width : Nat)
      (part : ∀ address, InRange base width address → KcovMetadataBytes layout address) :
      s0.data.dmem.loadInt base width =
        (s0.data.dmem.storeInt preemptCountAddress 4 (0x200 + preempt).toInt).loadInt base width := by
    apply frame.loadInt
    intro byte bound count
    exact ctx.coverageApart _ (.inl (part _ ⟨byte, bound, rfl⟩)) (.inr (.inr count))
  have task := field currentTaskAddress 8 (fun _ inside => .inl inside)
  have mode := field (layout.task + 0x6e0) 4 (fun _ inside => .inr (.inl inside))
  have capacity := field (layout.task + 0x6e4) 4 (fun _ inside => .inr (.inr (.inl inside)))
  have area := field (layout.task + 0x6e8) 8 (fun _ inside => .inr (.inr (.inr (.inl inside))))
  have softirq := field (layout.task + 0x704) 4 (fun _ inside => .inr (.inr (.inr (.inr inside))))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [KcovMetadata, load32, load64, ← task, ← mode, ← capacity, ← area, ← softirq]
      using metadata
  · simp only [load32, load32_store, Option.map_some, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
    rw [BitVec.add_comm]
  · intro active
    exact Kcov.buffer_frame layout _ _ (buffer active) _ frame
      (fun address storage count => ctx.coverageApart _ (.inr ⟨active, storage⟩) (.inr (.inr count)))

/-- The carried invariant first holds after the add to the preempt count. -/
theorem carried_start (ctx : Context layout preempt s0 kp skb nonce) {w : Window}
    (window : WindowAt s0.data.dmem (windowBase kp) w) {d : MachineData}
    (mem : d.dmem = s0.data.dmem.storeInt preemptCountAddress 4 (0x200 + preempt).toInt)
    (rsp : d.regs.rsp = s0.data.regs.rsp) (rbx : d.regs.rbx = s0.data.regs.rbx)
    (r12 : d.regs.r12 = s0.data.regs.r12) (r13 : d.regs.r13 = s0.data.regs.r13) :
    Carried layout preempt kp s0 w d := by
  refine ⟨?_, ?_, ?_, ?_, rsp, rbx, r12, r13⟩
  · rw [mem]; exact preempt_raised ctx
  · rw [mem]
    exact window.frame _ 4 _ (fun a count inside => ctx.windowPreempt a inside count)
  · intro a stack
    rw [mem]
    exact get_store_defined _ _ _ _ _ (ctx.stack a stack)
  · rw [mem]
    intro a outside
    exact storeInt_frame _ _ 4 _ a (fun count => outside (.inl (.inr (.inr count))))

/-- A rejection exit: the window is as it was and nothing is accepted. -/
theorem at_reject {o : Outcome} {d : MachineData} {history : List MachineState}
    (refused : o.accepted = false) (other : o.exit ≠ Range.donePC)
    (carried : Carried layout preempt kp s0 o.window d)
    (first : ∀ u ∈ history.dropLast, u.pc ∉ exits) :
    AtExit layout preempt kp s0 o ⟨⟨d, o.exit⟩, history⟩ :=
  ⟨rfl, first, by simp [accepted, refused, other], carried, fun done => absurd done other⟩

end

theorem head_segment (laid : RegionsLaidOut) (pcSite : PcSite) (cmp8Site : Cmp8Site)
    (constSite : ConstCmp8Site) : HeadSegment := by
  intro fetch layout preempt s kp skb nonce w reading ctx window
  have quiet : ∀ u ∈ [s], u.pc ∉ exits := by
    intro u hu
    rw [List.mem_singleton.mp hu, ctx.pc]
    decide
  show Eventually _ _ (⟨⟨s.data, s.pc⟩, [s]⟩ : Executed)
  rw [ctx.pc, ← regionPC_zero]
  -- +0 .. +31: the packet counter, the preempt count, the stored counter
  have theirs : s.data.dmem.loadInt (s.data.regs.rbx.toBitVec + 40#64) 8 =
      some (nonce.toNat : Int) := by rw [ctx.packet]; exact ctx.nonce
  have count := load32_raw _ _ preempt ctx.coverage.2.1
  have stored : (s.data.dmem.storeInt preemptCountAddress 4 (0x200 + preempt).toInt).loadInt
      (s.data.regs.r13.toBitVec + 136#64) 8 = some (w.counter.toNat : Int) := by
    rw [ctx.keypair]
    exact (window.frame _ 4 _ (fun a count inside => ctx.windowPreempt a inside count)).counterLoad
  apply region_step laid reading 0 5 (by decide) (by decide) s.data [s] quiet
    (r0 s.data nonce w.counter preempt theirs count stored)
  rintro ⟨⟨r1, z1, f1, y1, m1⟩, pc1⟩ h1 ⟨hr, hm, hp⟩ - q1
  dsimp only at hr hm hp
  subst hr hp
  have q1 := q1 (show Range.entry + 0x1f ∉ exits by decide)
  rw [show Range.entry + 0x1f = regionPC 5 by decide]
  -- site 1, then the counter-limit test
  refine call_step constSite laid reading ctx 5 "L_ffffffff810f4120" (by decide) rfl (by decide)
    (by decide) (by decide) _ h1 (w := w) ?_ q1 ?_
  · exact carried_start ctx window hm rfl rfl rfl rfl
  intro d2 h2 c2 rbp2 r142 _ _ _ q2
  dsimp only at rbp2 r142
  have counter2 : d2.regs.rbp.toBitVec = w.counter := by rw [rbp2]
  have nonce2 : d2.regs.r14.toBitVec = nonce := by rw [r142]
  apply region_step laid reading 6 2 (by decide) (by decide) d2 h2 q2 (r6 d2)
  rintro ⟨⟨r3, z3, f3, y3, m3⟩, pc3⟩ h3 ⟨hr, hm3, hp⟩ first3 q3
  dsimp only at hr hm3 hp
  subst hr hm3
  rw [counter2] at hp
  by_cases over : limit < w.counter
  · simp only [over, ↓reduceIte] at hp
    subst hp
    apply Eventually.done
    have rejects : Rejects w nonce := .inl over
    have outcome : validate w nonce = ⟨Range.rejectWindowPC, false, w⟩ := by
      simp only [validate, over, ↓reduceIte]
    simp only [HeadPost, rejects, ↓reduceIte]
    rw [outcome]
    exact at_reject (o := ⟨Range.rejectWindowPC, false, w⟩) rfl
      (show Range.rejectWindowPC ≠ Range.donePC by decide)
      (c2.move rfl rfl rfl rfl rfl) first3
  simp only [over, ↓reduceIte] at hp
  subst hp
  have q3 := q3 (show regionPC 6 + 7 + 6 ∉ exits by decide)
  rw [show regionPC 6 + 7 + 6 = regionPC 8 by decide]
  -- site 2, the arguments of site 3, site 3, then the packet-limit test
  refine call_step pcSite laid reading ctx 8 "L_ffffffff810f31f0" (by decide) rfl (by decide)
    (by decide) (by decide) _ h3 (w := w) ?_ q3 ?_
  · exact c2.move rfl rfl rfl rfl rfl
  intro d4 h4 c4 rbp4 r144 _ _ _ q4
  dsimp only at rbp4 r144
  apply region_step laid reading 9 2 (by decide) (by decide) d4 h4 q4 (r9 d4)
  rintro ⟨⟨r5, z5, f5, y5, m5⟩, pc5⟩ h5 ⟨hr, hm5, hp⟩ - q5
  dsimp only at hr hm5 hp
  subst hr hm5 hp
  have q5 := q5 (show regionPC 9 + 3 + 7 ∉ exits by decide)
  rw [show regionPC 9 + 3 + 7 = regionPC 11 by decide]
  refine call_step constSite laid reading ctx 11 "L_ffffffff810f4120" (by decide) rfl (by decide)
    (by decide) (by decide) _ h5 (w := w) ?_ q5 ?_
  · exact c4.move rfl rfl rfl rfl rfl
  intro d6 h6 c6 rbp6 r146 _ _ _ q6
  dsimp only at rbp6 r146
  have counter6 : d6.regs.rbp.toBitVec = w.counter := by rw [rbp6, rbp4, counter2]
  have nonce6 : d6.regs.r14.toBitVec = nonce := by rw [r146, r144, nonce2]
  apply region_step laid reading 12 2 (by decide) (by decide) d6 h6 q6 (r12 d6)
  rintro ⟨⟨r7, z7, f7, y7, m7⟩, pc7⟩ h7 ⟨hr, hm7, hp⟩ first7 q7
  dsimp only at hr hm7 hp
  subst hr hm7
  rw [nonce6] at hp
  by_cases last : limit ≤ nonce
  · simp only [last, ↓reduceIte] at hp
    subst hp
    apply Eventually.done
    have rejects : Rejects w nonce := .inr (.inl last)
    have outcome : validate w nonce = ⟨Range.rejectLimitPC, false, w⟩ := by
      simp only [validate, over, last, ↓reduceIte]
    simp only [HeadPost, rejects, ↓reduceIte]
    rw [outcome]
    exact at_reject (o := ⟨Range.rejectLimitPC, false, w⟩) rfl
      (show Range.rejectLimitPC ≠ Range.donePC by decide)
      (c6.move rfl rfl rfl rfl rfl) first7
  simp only [last, ↓reduceIte] at hp
  subst hp
  have q7 := q7 (show regionPC 12 + 7 + 6 ∉ exits by decide)
  rw [show regionPC 12 + 7 + 6 = regionPC 14 by decide]
  -- site 4, the spill of the incremented counter, site 5, then the too-old test
  refine call_step pcSite laid reading ctx 14 "L_ffffffff810f31f0" (by decide) rfl (by decide)
    (by decide) (by decide) _ h7 (w := w) ?_ q7 ?_
  · exact c6.move rfl rfl rfl rfl rfl
  intro d8 h8 c8 rbp8 r148 _ _ _ q8
  dsimp only at rbp8 r148
  have sp8 : d8.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec := by rw [c8.rsp]
  have counter8 : d8.regs.rbp.toBitVec = w.counter := by rw [rbp8, counter6]
  have nonce8 : d8.regs.r14.toBitVec = nonce := by rw [r148, nonce6]
  obtain ⟨x8, mapped8⟩ := c8.slot10Mapped
  rw [← sp8] at mapped8
  apply region_step laid reading 15 5 (by decide) (by decide) d8 h8 q8 (r15 d8 x8 mapped8)
  rintro ⟨⟨r9, z9, f9, y9, m9⟩, pc9⟩ h9 ⟨hr, hm9, hp⟩ - q9
  dsimp only at hr hm9 hp
  subst hr hp
  rw [sp8, nonce8] at hm9
  have q9 := q9 (show regionPC 15 + 4 + 7 + 3 + 3 + 5 ∉ exits by decide)
  rw [show regionPC 15 + 4 + 7 + 3 + 3 + 5 = regionPC 20 by decide]
  have s10_9 : m9.loadInt (s.data.regs.rsp.toBitVec + 0x10) 8 = some ((nonce + 1).toNat : Int) := by
    rw [hm9]
    exact load64_store _ _ _
  refine call_step cmp8Site laid reading ctx 20 "L_ffffffff810f40a0" (by decide) rfl (by decide)
    (by decide) (by decide) _ h9 (w := w) ?_ q9 ?_
  · exact c8.store ctx _ 8 _ (fun a => .inl ∘ slot10_stack) hm9
      (by rw [show m9 = _ from hm9]; exact c8.window.stackStore ctx _ 8 _ (fun a => slot10_stack))
      rfl rfl rfl rfl
  intro d10 h10 c10 rbp10 r1410 _ e10_10 _ q10
  dsimp only at rbp10 r1410 e10_10
  have counter10 : d10.regs.rbp.toBitVec = w.counter := by rw [rbp10, counter8]
  have old10 : d10.regs.r14.toBitVec = nonce + 0x1fc1 := by
    rw [r1410]
    show d8.regs.r14.toBitVec + 8129#64 = _
    rw [nonce8]
    rfl
  have s10_10 := e10_10.trans s10_9
  apply region_step laid reading 21 2 (by decide) (by decide) d10 h10 q10 (r21 d10)
  rintro ⟨⟨r11, z11, f11, y11, m11⟩, pc11⟩ h11 ⟨hr, hm11, hp⟩ first11 q11
  dsimp only at hr hm11 hp
  subst hr hm11
  rw [old10, counter10] at hp
  by_cases old : nonce + 0x1fc1 < w.counter
  · simp only [old, ↓reduceIte] at hp
    subst hp
    apply Eventually.done
    have rejects : Rejects w nonce := .inr (.inr old)
    have outcome : validate w nonce = ⟨Range.rejectWindowPC, false, w⟩ := by
      simp only [validate, over, last, old, ↓reduceIte]
    simp only [HeadPost, rejects, ↓reduceIte]
    rw [outcome]
    exact at_reject (o := ⟨Range.rejectWindowPC, false, w⟩) rfl
      (show Range.rejectWindowPC ≠ Range.donePC by decide)
      (c10.move rfl rfl rfl rfl rfl) first11
  simp only [old, ↓reduceIte] at hp
  subst hp
  have q11 := q11 (show regionPC 21 + 3 + 6 ∉ exits by decide)
  rw [show regionPC 21 + 3 + 6 = regionPC 23 by decide]
  -- site 6, the reload and the spill of the word index, site 7, then the in-window branch
  refine call_step pcSite laid reading ctx 23 "L_ffffffff810f31f0" (by decide) rfl (by decide)
    (by decide) (by decide) _ h11 (w := w) ?_ q11 ?_
  · exact c10.move rfl rfl rfl rfl rfl
  intro d12 h12 c12 rbp12 _ _ e10_12 _ q12
  dsimp only at rbp12 e10_12
  have sp12 : d12.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec := by rw [c12.rsp]
  have counter12 : d12.regs.rbp.toBitVec = w.counter := by rw [rbp12, counter10]
  have s10_12 := e10_12.trans s10_10
  obtain ⟨x12, mapped12⟩ := c12.slot18Mapped
  rw [← sp12] at mapped12
  apply region_step laid reading 24 6 (by decide) (by decide) d12 h12 q12
    (r24 d12 (nonce + 1) x12 (by rw [sp12]; exact s10_12) mapped12)
  rintro ⟨⟨r13, z13, f13, y13, m13⟩, pc13⟩ h13 ⟨hr, hm13, hp⟩ - q13
  dsimp only at hr hm13 hp
  subst hr hp
  rw [sp12] at hm13
  have q13 := q13 (show regionPC 24 + 5 + 3 + 3 + 3 + 4 + 5 ∉ exits by decide)
  rw [show regionPC 24 + 5 + 3 + 3 + 3 + 4 + 5 = regionPC 30 by decide]
  have s10_13 : m13.loadInt (s.data.regs.rsp.toBitVec + 0x10) 8 = some ((nonce + 1).toNat : Int) := by
    rw [hm13]
    exact (load_store_apart _ _ _ 8 8 _ (slot18_slot10 _)).trans s10_12
  have s18_13 : m13.loadInt (s.data.regs.rsp.toBitVec + 0x18) 8 =
      some (((nonce + 1) >>> 6).toNat : Int) := by
    rw [hm13]
    exact load64_store _ _ _
  refine call_step cmp8Site laid reading ctx 30 "L_ffffffff810f40a0" (by decide) rfl (by decide)
    (by decide) (by decide) _ h13 (w := w) ?_ q13 ?_
  · exact c12.store ctx _ 8 _ (fun a => .inl ∘ slot18_stack) hm13
      (by rw [show m13 = _ from hm13]; exact c12.window.stackStore ctx _ 8 _ (fun a => slot18_stack))
      rfl rfl rfl rfl
  intro d14 h14 c14 rbp14 r1414 r1514 e10_14 e18_14 q14
  dsimp only at rbp14 r1414 r1514 e10_14 e18_14
  have counter14 : d14.regs.rbp.toBitVec = w.counter := by rw [rbp14, counter12]
  have next14 : d14.regs.r14.toBitVec = nonce + 1 := by rw [r1414]
  have index14 : d14.regs.r15.toBitVec = (nonce + 1) >>> 6 := by rw [r1514]
  have s10_14 := e10_14.trans s10_13
  have s18_14 := e18_14.trans s18_13
  apply region_step laid reading 31 2 (by decide) (by decide) d14 h14 q14 (r31 d14)
  rintro ⟨⟨r15, z15, f15, y15, m15⟩, pc15⟩ h15 ⟨hr, hm15, hp⟩ - q15
  dsimp only at hr hm15 hp
  subst hr hm15
  rw [counter14, next14] at hp
  apply Eventually.done
  have passes : ¬Rejects w nonce := by
    rintro (h | h | h)
    · exact over h
    · exact last h
    · exact old h
  simp only [HeadPost, passes, ↓reduceIte]
  by_cases ahead : w.counter < nonce + 1
  · simp only [ahead, ↓reduceIte] at hp ⊢
    subst hp
    exact ⟨show regionPC 31 + 3 + 2 = advancePC by decide, c14.move rfl rfl rfl rfl rfl,
      q15 (show regionPC 31 + 3 + 2 ∉ exits by decide), counter14, index14, s10_14⟩
  · simp only [ahead, ↓reduceIte] at hp ⊢
    subst hp
    exact ⟨show regionPC 61 = tailPC by decide, c14.move rfl rfl rfl rfl rfl,
      q15 (show regionPC 61 ∉ exits by decide), s10_14, s18_14⟩

#print axioms head_segment
end Binary.C2
