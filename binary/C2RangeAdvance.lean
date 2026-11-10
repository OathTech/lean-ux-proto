import C2RangeSteps

/-! Work package 2 of result C2: the advance path, in three segments: the entry (+161,
call sites 8 and 9: the iteration count, capped, and the loop skipped when the two word
indices are equal), one iteration of the clear loop (+219, call sites 10 and 11), and the
store of the counter (+263, call site 12). -/
namespace Binary.C2
open Binary TrustBase
local instance : Labels := Binary.Image.linkedLabels

theorem advance_stores (laid : RegionsLaidOut) (pcSite : PcSite) : AdvanceStores := by
  intro fetch layout preempt s kp skb nonce w t e reading ctx at_
  obtain ⟨⟨d, pc0⟩, history⟩ := e
  obtain ⟨hpc, carried, quiet, s10, s18⟩ := at_
  dsimp only at hpc carried s10 s18
  subst hpc
  rw [show storePC = regionPC 58 by decide]
  apply call_step pcSite laid reading ctx 58 "L_ffffffff810f31f0" (by decide) rfl (by decide)
    (by decide) (by decide) d history carried quiet
  intro d1 h1 c1 _ _ _ e10 e18 q1
  have sp1 : d1.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec := by rw [c1.rsp]
  have k13 : d1.regs.r13.toBitVec = kp := by rw [c1.r13, ctx.keypair]
  have l10 : d1.dmem.loadInt (d1.regs.rsp.toBitVec + 16#64) 8 = some (t.toNat : Int) := by
    rw [sp1]; exact e10.trans s10
  have counter : d1.dmem.loadInt (d1.regs.r13.toBitVec + 136#64) 8 =
      some ((cleared w (top w t)).counter.toNat : Int) := by
    rw [k13]; exact c1.window.counterLoad
  apply region_step laid reading 59 2 (by decide) (by decide) d1 h1 q1 (r59 d1 t _ l10 counter)
  rintro ⟨⟨r2, z2, f2, y2, m2⟩, pc2⟩ h2 ⟨hr, hm, hp⟩ - q2
  dsimp only at hr hm hp
  subst hr hp
  rw [k13] at hm
  have q2 := q2 (show regionPC 59 + 5 + 7 ∉ exits by decide)
  apply Eventually.done
  refine ⟨show regionPC 59 + 5 + 7 = tailPC by decide, ?_, q2, ?_, ?_⟩
  · refine c1.store ctx (kp + 136#64) 8 t.toInt (fun a inside => .inr (counter_window inside)) hm
      ?_ rfl rfl rfl rfl
    rw [show m2 = d1.dmem.storeInt (kp + 136#64) 8 t.toInt from hm]
    exact c1.window.setCounter t
  · show m2.loadInt _ 8 = _
    rw [hm]
    exact (window_store_slot ctx _ _ _ _ _ (fun a => counter_window)
      (fun a => slot10_stack)).trans (e10.trans s10)
  · show m2.loadInt _ 8 = _
    rw [hm]
    exact (window_store_slot ctx _ _ _ _ _ (fun a => counter_window)
      (fun a => slot18_stack)).trans (e18.trans s18)

#print axioms advance_stores

/-- The capped iteration count as the image computes it (`cmp`, `cmova`). -/
theorem capped_count (x : BitVec 64) :
    (if 128#64 < x then 128#64 else x) = BitVec.ofNat 64 (min x.toNat 128) := by
  split <;> bv_omega

theorem advance_enters (laid : RegionsLaidOut) (pcSite : PcSite) (cmp8Site : Cmp8Site) :
    AdvanceEnters := by
  intro fetch layout preempt s kp skb nonce w t e reading ctx at_
  obtain ⟨⟨d, pc0⟩, history⟩ := e
  obtain ⟨hpc, carried, quiet, counter, index, s10⟩ := at_
  dsimp only at hpc carried counter index s10
  subst hpc
  rw [show advancePC = regionPC 33 by decide]
  apply call_step pcSite laid reading ctx 33 "L_ffffffff810f31f0" (by decide) rfl (by decide)
    (by decide) (by decide) d history carried quiet
  intro d1 h1 c1 rbp1 _ r151 e10 _ q1
  have sp1 : d1.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec := by rw [c1.rsp]
  obtain ⟨x, mapped⟩ := c1.slot18Mapped
  rw [← sp1] at mapped
  apply region_step laid reading 34 11 (by decide) (by decide) d1 h1 q1 (r34 d1 x mapped)
  rintro ⟨⟨r2, z2, f2, y2, m2⟩, pc2⟩ h2 ⟨hr, hm, hp⟩ - q2
  dsimp only at hr hm hp
  subst hr hp
  rw [sp1] at hm
  have q2 := q2 (show regionPC 34 + 3 + 3 + 5 + 4 + 3 + 5 + 5 + 3 + 3 + 3 + 4 ∉ exits by decide)
  rw [show regionPC 34 + 3 + 3 + 5 + 4 + 3 + 5 + 5 + 3 + 3 + 3 + 4 = regionPC 45 by decide]
  have index1 : d1.regs.r15.toBitVec = t >>> 6 := by rw [r151]; exact index
  have counter1 : d1.regs.rbp.toBitVec = w.counter := by rw [rbp1]; exact counter
  have s10_2 : m2.loadInt (s.data.regs.rsp.toBitVec + 0x10) 8 = some (t.toNat : Int) := by
    rw [hm]
    exact (load_store_apart _ _ _ 8 8 _ (slot18_slot10 _)).trans (e10.trans s10)
  have s18_2 : m2.loadInt (s.data.regs.rsp.toBitVec + 0x18) 8 = some ((t >>> 6).toNat : Int) := by
    rw [hm, index1]
    exact load64_store _ _ _
  refine call_step cmp8Site laid reading ctx 45 "L_ffffffff810f40a0" (by decide) rfl (by decide)
    (by decide) (by decide) _ h2 (w := w) ?_ q2 ?_
  · exact c1.store ctx _ 8 _ (fun a => .inl ∘ slot18_stack) hm
      (by rw [show m2 = _ from hm]; exact c1.window.stackStore ctx _ 8 _ (fun a => slot18_stack))
      rfl rfl rfl rfl
  intro d3 h3 c3 rbp3 r143 r153 e10_3 e18_3 q3
  dsimp only at rbp3 r143 r153 e10_3 e18_3
  have sp3 : d3.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec := by rw [c3.rsp]
  have s10_3 := e10_3.trans s10_2
  have s18_3 := e18_3.trans s18_2
  have current : d3.regs.r14.toBitVec = cur w := by
    rw [r143]
    show d1.regs.rbp.toBitVec >>> 6 = _
    rw [counter1]; rfl
  have iterations : d3.regs.r15.toBitVec = BitVec.ofNat 64 (top w t) := by
    rw [r153]
    show (if 128#64 < d1.regs.r15.toBitVec - d1.regs.rbp.toBitVec >>> 6 then 128#64
      else d1.regs.r15.toBitVec - d1.regs.rbp.toBitVec >>> 6) = _
    rw [index1, counter1, capped_count]; rfl
  apply region_step laid reading 46 2 (by decide) (by decide) d3 h3 q3
    (r46 d3 (t >>> 6) (by rw [sp3]; exact s18_3))
  rintro ⟨⟨r4, z4, f4, y4, m4⟩, pc4⟩ h4 ⟨hr, hm4, hp⟩ - q4
  dsimp only at hr hm4 hp
  subst hr hm4
  rw [current] at hp
  apply Eventually.done
  have zero : top w t = 0 ↔ t >>> 6 = cur w := by
    unfold top
    constructor
    · intro h; bv_omega
    · intro h; rw [h]; simp
  by_cases skipped : top w t = 0
  · simp only [skipped, ↓reduceIte]
    simp only [zero.mp skipped, ↓reduceIte] at hp
    subst hp
    refine ⟨show regionPC 58 = storePC by decide, ?_, q4 (show regionPC 58 ∉ exits by decide),
      s10_3, s18_3⟩
    rw [skipped]
    exact c3.move rfl rfl rfl rfl rfl
  · simp only [skipped, ↓reduceIte]
    simp only [show ¬(t >>> 6 = cur w) from fun h => skipped (zero.mpr h), ↓reduceIte] at hp
    subst hp
    exact ⟨show regionPC 46 + 5 + 2 = loopPC by decide, c3.move rfl rfl rfl rfl rfl,
      q4 (show regionPC 46 + 5 + 2 ∉ exits by decide), by omega, current,
      by rw [rbp3]; rfl, iterations, s10_3, s18_3⟩

#print axioms advance_enters

end Binary.C2
