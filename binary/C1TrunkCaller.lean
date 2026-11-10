import C1TrunkBelow
/-! Result C1, package 2: what both wrappers need of the caller's state, and
the memory facts their frames share (the four pushes, the callback, the
sequence increment, the locals). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
local instance : Labels := Image.linkedLabels

theorem eo_mono {p q : BitVec 64 → Prop} {a b : Mem 64} (imp : ∀ x, p x → q x)
    (eq : EqualOutside p a b) : EqualOutside q a b :=
  fun x hx => eq x (fun hp => hx (imp x hp))

/-- The caller's state at a wrapper's entry: an aligned stack with 200
mapped bytes below it, valid coverage state apart from that stack, and the
table's sequence word apart from both. `seq` is the word's value. -/
structure Caller (c : Context) (s : MachineData) (seq : BitVec 64) : Prop where
  aligned : s.regs.rsp.toNat % 8 = 0
  room : 200 ≤ s.regs.rsp.toNat
  below : Below s.dmem s.regs.rsp.toBitVec 200
  coverage : c.At s.dmem
  coverageStack : ∀ a, c.bytes a → ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 208 a
  metadataSeparate : ∀ a, c.writes a → ¬c.metadataBytes a
  preemptSeparate : ∀ a, c.writes a → ¬InRange preemptCountAddress 4 a
  seqWord : s.dmem.loadInt (s.regs.rdi.toBitVec+16) 8 = some (seq.toNat : Int)
  seqStack : ∀ a, InRange (s.regs.rdi.toBitVec+16) 8 a →
    ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 208 a
  seqCoverage : ∀ a, InRange (s.regs.rdi.toBitVec+16) 8 a → ¬c.bytes a

theorem pushed_frame (s : MachineData) :
    EqualOutside (InRange (s.regs.rsp.toBitVec - .ofNat 64 32) 32) s.dmem (pushed s) := by
  have step (m : Mem 64) (k : Nat) (hk : 8 ≤ k) (hk' : k ≤ 32) (v : Int) :
      EqualOutside (InRange (s.regs.rsp.toBitVec - .ofNat 64 32) 32) m
        (m.storeInt (s.regs.rsp.toBitVec - .ofNat 64 k) 8 v) :=
    eo_mono (fun x h => below_sub _ k 8 32 32 hk' (by omega) x h) (storeInt_frame m _ 8 v)
  intro x hx
  exact ((step _ 8 (by omega) (by omega) _ x hx).trans (step _ 16 (by omega) (by omega) _ x hx)).trans
    ((step _ 24 (by omega) (by omega) _ x hx).trans (step _ 32 (by omega) (by omega) _ x hx))

theorem pushed_mapped (s : MachineData) (a : BitVec 64) (k : Nat)
    (mapped : (s.dmem.loadInt a k).isSome = true) : ((pushed s).loadInt a k).isSome = true :=
  storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _
    (storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ mapped)))

theorem pushed_r13 (s : MachineData) :
    (pushed s).loadInt (s.regs.rsp.toBitVec - .ofNat 64 8) 8 = some (s.regs.r13.toNat : Int) := by
  show ((((s.dmem.storeInt (s.regs.rsp.toBitVec - .ofNat 64 8) 8 _).storeInt
    (s.regs.rsp.toBitVec - .ofNat 64 16) 8 _).storeInt
    (s.regs.rsp.toBitVec - .ofNat 64 24) 8 _).storeInt
    (s.regs.rsp.toBitVec - .ofNat 64 32) 8 _).loadInt (s.regs.rsp.toBitVec - .ofNat 64 8) 8 = _
  rw [below_load_store _ _ 8 8 32 8 _ (by decide) (by decide) (by decide),
    below_load_store _ _ 8 8 24 8 _ (by decide) (by decide) (by decide),
    below_load_store _ _ 8 8 16 8 _ (by decide) (by decide) (by decide)]
  exact load64_store _ _ _

theorem pushed_r12 (s : MachineData) :
    (pushed s).loadInt (s.regs.rsp.toBitVec - .ofNat 64 16) 8 = some (s.regs.r12.toNat : Int) := by
  show ((((s.dmem.storeInt (s.regs.rsp.toBitVec - .ofNat 64 8) 8 _).storeInt
    (s.regs.rsp.toBitVec - .ofNat 64 16) 8 _).storeInt
    (s.regs.rsp.toBitVec - .ofNat 64 24) 8 _).storeInt
    (s.regs.rsp.toBitVec - .ofNat 64 32) 8 _).loadInt (s.regs.rsp.toBitVec - .ofNat 64 16) 8 = _
  rw [below_load_store _ _ 16 8 32 8 _ (by decide) (by decide) (by decide),
    below_load_store _ _ 16 8 24 8 _ (by decide) (by decide) (by decide)]
  exact load64_store _ _ _

theorem pushed_rbp (s : MachineData) :
    (pushed s).loadInt (s.regs.rsp.toBitVec - .ofNat 64 24) 8 = some (s.regs.rbp.toNat : Int) := by
  show ((((s.dmem.storeInt (s.regs.rsp.toBitVec - .ofNat 64 8) 8 _).storeInt
    (s.regs.rsp.toBitVec - .ofNat 64 16) 8 _).storeInt
    (s.regs.rsp.toBitVec - .ofNat 64 24) 8 _).storeInt
    (s.regs.rsp.toBitVec - .ofNat 64 32) 8 _).loadInt (s.regs.rsp.toBitVec - .ofNat 64 24) 8 = _
  rw [below_load_store _ _ 24 8 32 8 _ (by decide) (by decide) (by decide)]
  exact load64_store _ _ _

theorem pushed_rbx (s : MachineData) :
    (pushed s).loadInt (s.regs.rsp.toBitVec - .ofNat 64 32) 8 = some (s.regs.rbx.toNat : Int) :=
  load64_store _ _ _

/-- The state the wrapper's coverage callback is called in. `fs` is the
wrapper's frame with the callee's return word: 48 (v4) or 56 (v6). -/
theorem Caller.ready {c : Context} {s : MachineData} {seq : BitVec 64} (caller : Caller c s seq)
    (fs : Nat) (lo : 40 ≤ fs) (hi : fs ≤ 56) (t : MachineData)
    (stack : t.regs.rsp.toBitVec - 8 = s.regs.rsp.toBitVec - .ofNat 64 fs)
    (aligned : t.regs.rsp.toNat % 8 = 0)
    (memory : t.dmem = pushed s) : CallsReady c t := by
  have inside (a : BitVec 64) (h : InRange (t.regs.rsp.toBitVec-8) 8 a) :
      InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 208 a := by
    rw [stack] at h
    exact below_sub _ fs 8 200 208 (by omega) (by omega) a h
  refine ⟨?_,aligned,?_,fun a read h => caller.coverageStack a read (inside a h),
    fun a w h => caller.coverageStack a (writes_bytes w) (inside a h),
    caller.metadataSeparate,caller.preemptSeparate⟩
  · rw [memory]
    apply state_frame c s.dmem (pushed s) caller.coverage _ (pushed_frame s)
    intro a read h
    exact caller.coverageStack a read (below_sub _ 32 32 200 208 (by omega) (by omega) a h)
  · rw [stack, memory]
    exact pushed_mapped s _ _ (caller.below.load fs 8 (by omega) (by omega))

/-- Memory after the wrapper's callback (`m2`) and after its locals and the
CALL of `add` (`m4`), against the caller's memory. -/
structure Frames (c : Context) (s : MachineData) (seq : BitVec 64) (fs : Nat) (m2 m4 : Mem 64) : Prop where
  callback : EqualOutside (fun a => InRange (s.regs.rsp.toBitVec - .ofNat 64 fs) 8 a ∨ c.writes a)
    (pushed s) m2
  coverage : c.At m2
  locals : EqualOutside (InRange (s.regs.rsp.toBitVec - .ofNat 64 fs) (fs-32))
    (m2.storeInt (s.regs.rdi.toBitVec+16) 8 (1+seq).toInt) m4

section
variable {c : Context} {s : MachineData} {seq : BitVec 64} {fs : Nat} {m2 m4 : Mem 64}

/-- A range apart from the stack window and the coverage buffer is unchanged
by the pushes and the callback. -/
theorem Frames.before (frames : Frames c s seq fs m2 m4) (lo : 40 ≤ fs) (hi : fs ≤ 56)
    (base : BitVec 64) (n : Nat)
    (stack : ∀ a, InRange base n a → ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 200 a)
    (buffer : ∀ a, InRange base n a → ¬c.writes a) :
    m2.loadInt base n = s.dmem.loadInt base n := by
  rw [← frames.callback.loadInt base n (fun i hi' h => by
    rcases h with h | h
    · exact stack _ ⟨i,hi',rfl⟩ (below_sub _ fs 8 200 200 (by omega) (by omega) _ h)
    · exact buffer _ ⟨i,hi',rfl⟩ h)]
  exact ((pushed_frame s).loadInt base n (fun i hi' h =>
    stack _ ⟨i,hi',rfl⟩ (below_sub _ 32 32 200 200 (by omega) (by omega) _ h))).symm

theorem Frames.seqBefore (caller : Caller c s seq) (frames : Frames c s seq fs m2 m4)
    (lo : 40 ≤ fs) (hi : fs ≤ 56) :
    m2.loadInt (s.regs.rdi.toBitVec+16) 8 = some (seq.toNat : Int) := by
  rw [← frames.callback.loadInt _ 8 (fun i hi' h => by
    rcases h with h | h
    · exact caller.seqStack _ ⟨i,hi',rfl⟩ (below_sub _ fs 8 200 208 (by omega) (by omega) _ h)
    · exact caller.seqCoverage _ ⟨i,hi',rfl⟩ (writes_bytes h)),
    ← (pushed_frame s).loadInt _ 8 (fun i hi' h =>
      caller.seqStack _ ⟨i,hi',rfl⟩ (below_sub _ 32 32 200 208 (by omega) (by omega) _ h))]
  exact caller.seqWord

theorem Frames.seqAfter (caller : Caller c s seq) (frames : Frames c s seq fs m2 m4)
    (lo : 40 ≤ fs) (hi : fs ≤ 56) :
    m4.loadInt (s.regs.rdi.toBitVec+16) 8 = some ((1+seq).toNat : Int) := by
  rw [← frames.locals.loadInt _ 8 (fun i hi' h =>
    caller.seqStack _ ⟨i,hi',rfl⟩ (below_sub _ fs (fs-32) 200 208 (by omega) (by omega) _ h))]
  exact load64_store _ _ _

theorem Frames.coverageAfter (caller : Caller c s seq) (frames : Frames c s seq fs m2 m4)
    (lo : 40 ≤ fs) (hi : fs ≤ 56) : c.At m4 := by
  apply state_frame c m2 m4 frames.coverage _ ((storeInt_frame m2 _ 8 _).trans frames.locals)
  intro a read h
  rcases h with h | h
  · exact caller.seqCoverage a h read
  · exact caller.coverageStack a read (below_sub _ fs (fs-32) 200 208 (by omega) (by omega) a h)

/-- A word saved by the pushes is still there at the CALL of `add`. -/
theorem Frames.saved (caller : Caller c s seq) (frames : Frames c s seq fs m2 m4)
    (lo : 40 ≤ fs) (hi : fs ≤ 56) (k : Nat) (hk : 8 ≤ k) (hk' : k ≤ 32) :
    m4.loadInt (s.regs.rsp.toBitVec - .ofNat 64 k) 8 = (pushed s).loadInt (s.regs.rsp.toBitVec - .ofNat 64 k) 8 := by
  have wide (i : Nat) (hi' : i < 8) :
      InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 208 (s.regs.rsp.toBitVec - .ofNat 64 k + .ofNat 64 i) :=
    below_sub _ k 8 200 208 (by omega) (by omega) _ ⟨i,hi',rfl⟩
  rw [← frames.locals.loadInt _ 8 (fun i hi' h =>
      below_disjoint _ k 8 fs (fs-32) (by omega) (by omega) (by omega) _ ⟨i,hi',rfl⟩ h),
    ← (storeInt_frame m2 _ 8 _).loadInt _ 8 (fun i hi' h => caller.seqStack _ h (wide i hi')),
    ← frames.callback.loadInt _ 8 (fun i hi' h => by
      rcases h with h | h
      · exact below_disjoint _ k 8 fs 8 (by omega) (by omega) (by omega) _ ⟨i,hi',rfl⟩ h
      · exact caller.coverageStack _ (writes_bytes h) (wide i hi'))]

/-- The whole write frame from the caller's memory to the CALL of `add`. -/
theorem Frames.total (frames : Frames c s seq fs m2 m4) (lo : 40 ≤ fs) (hi : fs ≤ 56) :
    EqualOutside (fun a => InRange (s.regs.rsp.toBitVec - .ofNat 64 fs) fs a ∨
      InRange (s.regs.rdi.toBitVec+16) 8 a ∨ c.writes a) s.dmem m4 := by
  intro x hx
  refine ((pushed_frame s) x (fun h => hx (.inl (below_sub _ 32 32 fs fs (by omega) (by omega) x h)))).trans
    ((frames.callback x (fun h => hx ?_)).trans
    (((storeInt_frame m2 _ 8 _) x (fun h => hx (.inr (.inl h)))).trans
    (frames.locals x (fun h => hx (.inl (below_sub _ fs (fs-32) fs fs (by omega) (by omega) x h))))))
  rcases h with h | h
  · exact .inl (below_sub _ fs 8 fs fs (by omega) (by omega) x h)
  · exact .inr (.inr h)
end

#print axioms Caller.ready
#print axioms Frames.saved
#print axioms Frames.total
end C1Trunk
