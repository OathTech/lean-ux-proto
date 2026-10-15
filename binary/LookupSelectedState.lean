import LookupHelperCall

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation PeerCountPhase

private theorem first_cells (c : Config) (entries : List IndexEntry) :
    firstIndex c.query (entries.map fun e => (ownerAddress c e.owner, e)) =
      (entries.find? (fun e => e.index == c.query)).map (fun e => (ownerAddress c e.owner, e)) := by
  induction entries with
  | nil => rfl
  | cons e rest ih =>
    cases hit : (e.index == c.query) <;> simp [firstIndex, List.find?, hit, ih]

/-- Selection is by the first matching index and its kind; it requires
    neither unique indices nor a live/non-NULL owner word. -/
theorem selected_stop (c : Config) (v : View) (s : MachineState) (owner : IndexOwner)
    (focused : selected c v.bucket = some owner) (stop : BucketStop c.query c.kinds (cells c v) s) :
    s.pc = Image.Lookup.entry+0xad ∧ s.data.regs.rbx.toBitVec = ownerAddress c owner ∧ v.bucket ≠ [] := by
  cases found : v.bucket.find? (fun e => e.index == c.query) with
  | none => simp [selected, found] at focused
  | some entry =>
    cases allowed : c.kinds.contains entry.kind with
    | false => simp [selected, found, allowed] at focused
    | true =>
      have ownerEq : entry.owner = owner := by simpa [selected, found, allowed] using focused
      have stopped := stop
      simp only [BucketStop, cells, first_cells, found, Option.map_some, allowed, ite_true] at stopped
      refine ⟨stopped.1, by simpa only [ownerEq] using stopped.2, ?_⟩
      intro empty
      rw [empty] at found
      cases found

/-- The no-owner branch retains both actual machine exits: exhaustion's
    callback at +6c and first-match wrong-kind at +71. -/
theorem selected_stop_none (c : Config) (v : View) (s : MachineState)
    (focused : selected c v.bucket = none) (stop : BucketStop c.query c.kinds (cells c v) s) :
    s.pc = Image.Lookup.entry+0x6c ∨ s.pc = Image.Lookup.entry+0x71 := by
  cases found : v.bucket.find? (fun e => e.index == c.query) with
  | none =>
    simp only [BucketStop, cells, first_cells, found, Option.map_none] at stop
    exact .inl stop.1
  | some entry =>
    cases allowed : c.kinds.contains entry.kind with
    | false =>
      simp only [BucketStop, cells, first_cells, found, Option.map_some, allowed, Bool.false_eq_true, ite_false] at stop
      exact .inr stop.1
    | true => simp [selected, found, allowed] at focused

theorem result_latest (c : Config) (entries : List IndexEntry)
    (source : List MirrorHistory.Point) (world : World) :
    (LookupSearch.result c.kinds c.query entries source world).1.2.getLast?.map (·.world) =
      some (LookupSearch.result c.kinds c.query entries source world).2 := by
  simp [LookupSearch.result, LookupSearch.finish]

/-- Exact selected-bucket state facts recovered from the witnessed entry
    and the loop theorem. Its peer word may be NULL or point to a dead peer. -/
theorem selected_after_bucket (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (returnAddress : UInt64) (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v)
    (t : Executed) (afterBucket : AfterBucket c world s coverage preempt v t)
    (owner : IndexOwner) (focused : c.focus.owner = some owner) :
    t.machine.pc = Image.Lookup.entry+0xad ∧
    t.machine.data.regs.rbx.toBitVec = ownerAddress c owner ∧
    t.machine.data.regs.rsp = s.regs.rsp-40 ∧
    LookupCoverage.CallsReady ⟨coverage, preempt, v⟩ (512+preempt) t.machine.data ∧
    LookupCoverage.Context.CompareAllowed ⟨coverage, preempt, v⟩ (512+preempt) ∧
    t.machine.data.dmem.loadInt (ownerAddress c owner) 8 =
      some ((OwnerWord.pointer c.peers c.focus.peer).toNat : Int) ∧
    ∃ delta,
      observe c.rxSection t.history = .ok ([entryPoint s] ++ delta) ∧
      helperActive ([entryPoint s] ++ delta) = false ∧
      lastHelperReturn ([entryPoint s] ++ delta) = none ∧
      StableExtension [⟨s, Image.Lookup.entry⟩] t.history := by
  obtain ⟨head, atHead, _, stop, frame, delta, observed, raw, matched, aligned, related, stable, tags, _⟩ := afterBucket
  have selectedEq := entry.focus.1.trans focused
  obtain ⟨pc, ownerReg, nonempty⟩ := selected_stop c v t.machine owner selectedEq stop
  have inactive : helperActive ([entryPoint s] ++ delta) = false := by
    rw [helperActive_append_decisions _ _ tags]
    rfl
  have noReturn : lastHelperReturn ([entryPoint s] ++ delta) = none :=
    lastHelperReturn_append_decisions _ _ tags rfl
  have projected : project c (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).2 = some v := by
    calc
      _ = project c {world with steps := (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).2.steps} :=
        congrArg (project c) (LookupSearch.result_world _ _ _ _ _)
      _ = project c world := rfl
      _ = some v := entry.projected
  obtain ⟨view, viewProjection, physical⟩ := related.2.1
  have same : view = v := Option.some.inj (viewProjection.symm.trans projected)
  subst view
  have ownerField := physical.2.2.1
  simp only [focused] at ownerField
  obtain ⟨word, value, loaded⟩ := ownerField
  have wordValue : v.ownerWord = some c.focus.peer := by simpa only [EntryFocus, focused] using entry.focus.2
  have wordEq : word = c.focus.peer := Option.some.inj (value.symm.trans wordValue)
  subst word
  have ownerOrdinary := ownerPending_none ([entryPoint s] ++ delta) t.machine noReturn
  simp only [OwnerFieldAt, ownerOrdinary, OwnerWord.Field] at loaded
  have baseStack : (bucketExitBase head.machine.data c.query (cells c v)).regs.rsp = head.machine.data.regs.rsp := by
    unfold bucketExitBase
    split <;> simp [kindBase, MachineData.setReg, Reg64s.set, Reg64s.set64]
  exact ⟨pc, ownerReg, frame.stack.trans (baseStack.trans atHead.stack), frame.ready,
    ⟨rfl, nonempty⟩, loaded, delta, observed, inactive, noReturn, atHead.stable.trans stable⟩

#print axioms selected_stop
#print axioms selected_stop_none
#print axioms result_latest
#print axioms selected_after_bucket
end Binary.LookupRelation
