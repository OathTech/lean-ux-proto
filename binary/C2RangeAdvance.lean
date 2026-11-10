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

end Binary.C2
