import C2RangeSteps

/-! Work package 2 of result C2: the tail of the range (+280 to the exit at +324, call
site 13): the spilled index and counter are reloaded and masked, `bts` tests and sets
the bit, `%esi` gets the unlock argument, `setb` leaves the old bit in `%bpl`. -/
namespace Binary.C2
open Binary TrustBase
local instance : Labels := Binary.Image.linkedLabels

/-- `setBit` with the changed word named once. -/
theorem setBit_eq (w : Window) (t : BitVec 64) :
    setBit w t = Window.mk w.counter (fun i =>
      if i = ((t >>> 6) &&& 127).toNat then
        w.words ((t >>> 6) &&& 127).toNat ||| (1#64 <<< (t &&& 63).toNat)
      else w.words i) := by
  unfold setBit
  congr 1
  funext i
  split
  · rename_i at_; rw [at_]
  · rfl

theorem tail_segment (laid : RegionsLaidOut) (pcSite : PcSite) : TailSegment := by
  intro fetch layout preempt s kp skb nonce w t e reading ctx at_
  obtain ⟨⟨d, pc0⟩, history⟩ := e
  obtain ⟨hpc, carried, quiet, s10, s18⟩ := at_
  dsimp only at hpc carried s10 s18
  subst hpc
  rw [show tailPC = regionPC 61 by decide]
  apply call_step pcSite laid reading ctx 61 "L_ffffffff810f31f0" (by decide) rfl (by decide)
    (by decide) (by decide) d history carried quiet
  intro d1 h1 c1 _ _ _ e10 e18 q1
  have sp1 : d1.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec := by rw [c1.rsp]
  have l18 : d1.dmem.loadInt (d1.regs.rsp.toBitVec + 24#64) 8 = some ((t >>> 6).toNat : Int) := by
    rw [sp1]; exact e18.trans s18
  have l10 : d1.dmem.loadInt (d1.regs.rsp.toBitVec + 16#64) 8 = some (t.toNat : Int) := by
    rw [sp1]; exact e10.trans s10
  apply region_step laid reading 62 2 (by decide) (by decide) d1 h1 q1 (r62 d1 t (t >>> 6) l18 l10)
  rintro ⟨⟨r2, z2, f2, y2, m2⟩, pc2⟩ h2 ⟨hr, hm, hp⟩ - q2
  dsimp only at hr hm hp
  subst hr hm hp
  have q2 := q2 (show regionPC 62 + 5 + 5 ∉ exits by decide)
  rw [show regionPC 62 + 5 + 5 = regionPC 64 by decide]
  apply region_step laid reading 64 1 (by decide) (by decide) _ h2 q2 (r64 _)
  rintro ⟨⟨r3, z3, f3, y3, m3⟩, pc3⟩ h3 ⟨hr, hm, hp⟩ - q3
  dsimp only at hr hm hp
  subst hr hm hp
  have q3 := q3 (show regionPC 64 + 4 ∉ exits by decide)
  rw [show regionPC 64 + 4 = regionPC 65 by decide]
  apply region_step laid reading 65 1 (by decide) (by decide) _ h3 q3 (r65 _)
  rintro ⟨⟨r4, z4, f4, y4, m4⟩, pc4⟩ h4 ⟨hr, hm, hp⟩ - q4
  dsimp only at hr hm hp
  subst hr hm hp
  have q4 := q4 (show regionPC 65 + 4 ∉ exits by decide)
  rw [show regionPC 65 + 4 = regionPC 66 by decide]
  apply region_step laid reading 66 1 (by decide) (by decide) _ h4 q4 (r66 _)
  rintro ⟨⟨r5, z5, f5, y5, m5⟩, pc5⟩ h5 ⟨hr, hm, hp⟩ - q5
  dsimp only at hr hm hp
  subst hr hm hp
  have q5 := q5 (show regionPC 66 + 8 ∉ exits by decide)
  rw [show regionPC 66 + 8 = regionPC 67 by decide]
  have index : ((t >>> 6) &&& 127).toNat < 128 := by
    rw [BitVec.toNat_and, show BitVec.toNat (127 : BitVec 64) = 127 from rfl, and127]; omega
  have offset : (t &&& 63).toNat < 64 := by
    rw [BitVec.toNat_and, show BitVec.toNat (63 : BitVec 64) = 63 from rfl, and63]; omega
  have address : d1.regs.r13.toBitVec + 8#64 * ((t >>> 6) &&& (127 : BitVec 64)) + 144#64 =
      wordAddress kp ((t >>> 6) &&& 127).toNat := by
    rw [c1.r13, ctx.keypair, word_address]
  have word := c1.window.wordLoad _ index
  rw [← address] at word
  apply region_step laid reading 67 1 (by decide) (by decide) _ h5 q5
    (r67 _ (w.words ((t >>> 6) &&& 127).toNat) (by exact offset) (by exact word))
  rintro ⟨⟨r6, z6, f6, y6, m6⟩, pc6⟩ h6 ⟨hr, hm, hcf, hp⟩ - q6
  dsimp only at hr hm hcf hp
  subst hr hm hp
  have q6 := q6 (show regionPC 67 + 4 ∉ exits by decide)
  rw [show regionPC 67 + 4 = regionPC 68 by decide]
  apply region_step laid reading 68 2 (by decide) (by decide) _ h6 q6 (r68 _)
  rintro ⟨d7, pc7⟩ h7 ⟨rsi, rbp, rsp, rbx, r12, r13, hm, hp⟩ first -
  dsimp only at rsi rbp rsp rbx r12 r13 hm hp
  subst hp
  apply Eventually.done
  have window : WindowAt d7.dmem (windowBase kp) (setBit w t) := by
    have stored := c1.window.setWord _ index
      (w.words ((t >>> 6) &&& 127).toNat ||| (1#64 <<< (t &&& 63).toNat))
    rw [← address] at stored
    rw [hm, setBit_eq]
    exact stored
  refine ⟨show regionPC 68 + 5 + 4 = Range.donePC by decide, first, ?_, ?_, fun _ => ?_⟩
  · show accepted ⟨d7, _⟩ = !seen w t
    have old : f6.cf = seen w t := hcf
    simp only [accepted, rbp, old]
    rw [show (regionPC 68 + 5 + 4 == Range.donePC) = true by decide]
    cases seen w t <;> simp
  · exact c1.store ctx _ 8 _ (fun a inside => .inr (word_window index (address ▸ inside))) hm
      window rsp rbx r12 r13
  · show d7.regs.rsi.toNat % 2 ^ 32 = 0x200
    rw [rsi]; rfl

#print axioms tail_segment
end Binary.C2
