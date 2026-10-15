import Leanux.Proofs.WG.Queues.RxPollStampSafety
import Leanux.Proofs.WG.Queues.RxRingNapi

/-! The receive iteration's capture/removal/release phases. A pending stamp
may remain in a failed prefix; only normal iteration return restores Ready. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def removedStamp : Event → Option PacketStamp | .removed _ _ s => some s | _ => none
def removedStamps (h : List Event) := h.filterMap removedStamp
def Released (h : List Event) (s : PacketStamp) :=
  AccessEvent.Released ((h.filterMap accessEvent).filterMap LifetimeEvent.packet?) s

inductive PhaseKind where
  | ready
  | captured (skb : SkbId) (stamp : PacketStamp)
  | pending (skb : SkbId) (stamp : PacketStamp)

def PhaseExtra : PhaseKind → List Event → World → Prop
  | .ready, h, _ => ∀ s ∈ removedStamps h, Released h s
  | .captured skb stamp, h, w => packetStamp w skb = stamp ∧
      stamp ∉ removedStamps h ∧ ∀ s ∈ removedStamps h, Released h s
  | .pending skb stamp, h, w => packetStamp w skb = stamp ∧
      ∀ s ∈ removedStamps h, s ≠ stamp → Released h s

structure Phase (kind : PhaseKind) (h : List Event) (w : World) : Prop where
  allocation : AllocationInv (h.filterMap accessEvent) w
  distinct : (removedStamps h).Nodup
  extra : PhaseExtra kind h w

def StampSafe (h : List Event) := LifetimeEvent.Safe (h.filterMap accessEvent) ∧
  (removedStamps h).Nodup

theorem Phase.safe (hi : Phase kind h w) : StampSafe h := ⟨hi.allocation.safe, hi.distinct⟩

theorem released_mono (h tail : List Event) (s : PacketStamp) (hs : Released h s) :
    Released (h ++ tail) s := by
  simp only [Released, List.filterMap_append, AccessEvent.released_append] at *
  exact Or.inl hs

theorem stamp_cell (w v : World) (skb : SkbId) (he : RxRing.cell v = RxRing.cell w) :
    packetStamp v skb = packetStamp w skb := by
  have hh := congrArg (fun c : Option (Nat × PtrRing SkbId) => (c.map Prod.fst).getD 0) he
  simpa only [RxRing.cell, packetStamp, Option.map_map, Function.comp_def] using
    congrArg (fun n => (n, skb + 1)) hh

theorem Phase.transport (hi : Phase kind h w) (tail : List Event)
    (ha : AllocationInv ((h ++ tail).filterMap accessEvent) v)
    (hm : removedStamps (h ++ tail) = removedStamps h)
    (hc : RxRing.cell v = RxRing.cell w) : Phase kind (h ++ tail) v := by
  refine ⟨ha, hm ▸ hi.distinct, ?_⟩
  cases kind with
  | ready => exact fun s hs => released_mono h tail s (hi.extra s (hm ▸ hs))
  | captured skb stamp =>
    refine ⟨(stamp_cell w v skb hc).trans hi.extra.1, ?_, ?_⟩
    · simpa only [hm] using hi.extra.2.1
    · exact fun s hs => released_mono h tail s (hi.extra.2.2 s (hm ▸ hs))
  | pending skb stamp =>
    exact ⟨(stamp_cell w v skb hc).trans hi.extra.1,
      fun s hs hn => released_mono h tail s (hi.extra.2 s (hm ▸ hs) hn)⟩

theorem phase_project (kind : PhaseKind) (g : Obs α) (a : MixedM β)
    (p : α → β) (hp : ProjectsUnderTo AllocationInv accessEvent p g a)
    (ha : PrefixPreserves AllocationInv LifetimeEvent.Safe a)
    (he : ErasesPrefix a original) (hc : SameView RxRing.cell original)
    (hm : HistoryFrame removedStamp g) (hg : Appends g) :
    PrefixPreserves (Phase kind) StampSafe g := by
  intro w h hi
  obtain ⟨tail, ht⟩ := hg w h
  have hs := hp.preserves ha w h hi.allocation
  have hj := hp w h hi.allocation
  refine ⟨tail, ht, ⟨hs.1, ?_⟩, ?_⟩
  · simpa only [removedStamps, hm w h] using hi.distinct
  · cases hr : (runPrefix g w h).1 with
    | error e => trivial
    | ok out =>
      have ho : original.run w = .ok (p out.1, out.2) := by
        rw [← he w (h.filterMap accessEvent), hj, hr]; rfl
      have hav : AllocationInv ((h ++ tail).filterMap accessEvent) out.2 := by
        simpa only [hr, ht] using hs.2
      simpa only [hr, ht] using hi.transport tail hav
        (by simpa only [← ht, removedStamps] using hm w h) (hc w _ _ ho)

theorem phase_access (kind : PhaseKind) (a : MixedM α)
    (ha : PrefixPreserves AllocationInv LifetimeEvent.Safe a)
    (he : ErasesPrefix a original) (hc : SameView RxRing.cell original) :
    PrefixPreserves (Phase kind) StampSafe (access a) :=
  phase_project kind _ a id (access_projects ha).to_mapped ha he hc
    (fun w h => focusPrefix_other Event.access accessEvent removedStamp (fun _ => rfl) a w h)
    (access_appends a)

theorem phase_lift (kind : PhaseKind) (a : M α) (ha : SameKernel a) :
    PrefixPreserves (Phase kind) StampSafe (liftPrefix a) :=
  phase_project kind _ _ id (projectsUnderTo_lift _ a)
    (allocation_kernel a ha) (erasesPrefix_lift a) (RxRing.kernel ha)
    (HistoryFrame.lift _ a) (Appends.lift a)

theorem phase_emit (kind : PhaseKind) (e : Event)
    (ha : accessEvent e = none) (hm : removedStamp e = none) :
    PrefixPreserves (Phase kind) StampSafe (emitPrefix e) :=
  phase_project kind _ (pure ()) id (projectsUnder_emit accessEvent e ha).to_mapped
    (PrefixPreserves.pure (fun _ _ hi => hi.safe) ()) (erasesPrefix_pure ())
    (SameView.pure _ ()) (HistoryFrame.emit e hm) (emit_appends e)

theorem phase_capture (skb : SkbId) :
    PrefixEnsures (Phase .ready) StampSafe (capture skb)
      (fun out => Phase (.captured skb out.2)) := by
  intro w h hi
  obtain ⟨tail, ht⟩ := capture_appends skb w h
  have hs := (capture_access skb).underTo.preserves (AmbientContracts.drop (allocationAmbient.getRx (fun _ => True) skb)) w h hi.allocation
  have hm : HistoryFrame removedStamp (capture skb) := by
    intro w h
    rw [capture_run]
    cases (getRxSkb skb).run w <;> simp [removedStamp, List.filterMap_append]
  refine ⟨tail, ht, ⟨hs.1, by simpa only [removedStamps, hm w h] using hi.distinct⟩, ?_⟩
  cases hr : (runPrefix (capture skb) w h).1 with
  | error e => trivial
  | ok out =>
    obtain ⟨hw, hstamp, hfresh⟩ := capture_fresh skb w out.2 h out.1.1 out.1.2 hi.allocation hr
    have ha := hs.2
    simp only [hr] at ha
    have hrdy := hi.transport tail (by simpa only [← ht] using ha)
      (by simpa only [← ht, removedStamps] using hm w h) (congrArg RxRing.cell hw)
    refine ⟨ha, ?_, ?_⟩
    · simpa only [ht] using hrdy.distinct
    · refine ⟨by rw [hw, hstamp], ?_, ?_⟩
      · intro hin
        have old : out.1.2 ∈ removedStamps h := by simpa only [removedStamps, hm w h] using hin
        exact hfresh (hi.extra _ old)
      · simpa only [ht, PhaseExtra] using hrdy.extra

theorem phase_mark (pid n skb : Nat) (stamp : PacketStamp) :
    PrefixEnsures (Phase (.captured skb stamp)) StampSafe
      (emitPrefix (.removed n skb stamp)) (fun _ => Phase (.pending skb stamp)) := by
  intro w h hi
  have hm : removedStamps (h ++ [.removed n skb stamp]) = removedStamps h ++ [stamp] := by
    simp [removedStamps, removedStamp, List.filterMap_append]
  have ha : (h ++ [Event.removed n skb stamp]).filterMap accessEvent = h.filterMap accessEvent := by
    simp [accessEvent, List.filterMap_append]
  have hd : (removedStamps (h ++ [.removed n skb stamp])).Nodup := by
    rw [hm]
    apply List.nodup_append.mpr
    exact ⟨hi.distinct, by simp, fun a ha b hb => by simp only [List.mem_singleton] at hb; subst b; intro eq; subst a; exact hi.extra.2.1 ha⟩
  refine ⟨[.removed n skb stamp], rfl, ⟨by simpa only [runPrefix_emit, ha] using hi.allocation.safe, hd⟩, ?_⟩
  change Phase (.pending skb stamp) (h ++ [.removed n skb stamp]) w
  refine ⟨ha ▸ hi.allocation, hd, hi.extra.1, ?_⟩
  intro s hs hn
  rw [hm, List.mem_append, List.mem_singleton] at hs
  rcases hs with old | fresh
  · exact released_mono h _ s (hi.extra.2.2 s old)
  · exact False.elim (hn fresh)

theorem phase_drop (pid n skb : Nat) (stamp : PacketStamp) :
    PrefixEnsures (Phase (.captured skb stamp)) StampSafe (drop pid n skb stamp)
      (fun _ => Phase (.pending skb stamp)) := by
  unfold drop
  apply PrefixEnsures.bind
    (phase_access _ _ (rxDropPeekedPrefix_preserves allocationAmbient pid)
      (rxDropPeekedPrefix_erases pid)
      ((RxRing.getPeer_cell pid).bind (fun _ => (RxRing.getPeer_cell pid).bind
        (fun _ => RxRing.setPeer_frame _ _))))
  intro _
  exact phase_mark pid n skb stamp

theorem phase_free (skb : SkbId) (stamp : PacketStamp) :
    PrefixEnsures (Phase (.pending skb stamp)) StampSafe (access (freeRxSkbPrefix skb))
      (fun _ => Phase .ready) := by
  intro w h hi
  obtain ⟨tail, ht, hs, hp⟩ := phase_access (.pending skb stamp) _
    (allocationRx.free skb) (freeRxSkbPrefix_erases skb) (RxRing.freeRx_frame skb) w h hi
  refine ⟨tail, ht, hs, ?_⟩
  cases hr : (runPrefix (access (freeRxSkbPrefix skb)) w h).1 with
  | error e => trivial
  | ok out =>
    simp only [hr] at hp
    refine ⟨hp.allocation, hp.distinct, ?_⟩
    intro s hm
    by_cases he : s = stamp
    · subst s
      cases hg : (getRxSkb skb).run w with
      | error e => simp only [free_run, hg] at hr; contradiction
      | ok p =>
        simp [free_run, hg, Released, List.filterMap_append, accessEvent,
          LifetimeEvent.packet?, AccessEvent.Released, hi.extra.1]
    · exact hp.extra.2 s hm he

theorem consume_removed (pid n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    HistoryFrame removedStamp (consume pid n skb stamp pkt ep) := by
  unfold consume
  apply HistoryFrame.bind
    (fun w h => focusPrefix_other Event.access accessEvent removedStamp (fun _ => rfl) _ w h)
  intro out
  cases out with
  | none => exact HistoryFrame.pure _ _
  | some bytes => exact HistoryFrame.bind (HistoryFrame.emit _ rfl) (fun _ => HistoryFrame.pure _ _)

theorem phase_consume (kind : PhaseKind) (pid n skb : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (ep : Endpoint) :
    PrefixPreserves (Phase kind) StampSafe (consume pid n skb stamp pkt ep) :=
  phase_project kind _ _ _ (consume_access pid n skb stamp pkt ep)
    (consumeDataDonePrefix_preserves_ambient allocationAmbient allocationTx allocationRx pid pkt ep)
    (consumeDataDonePrefix_erases pid pkt ep) (RxRing.consumeDataDone_cell pid pkt ep)
    (consume_removed pid n skb stamp pkt ep) (consume_appends pid n skb stamp pkt ep)

theorem flush_removed (entries : List Entry) : HistoryFrame removedStamp (flush entries) := by
  induction entries with
  | nil => exact HistoryFrame.pure _ _
  | cons e rest ih =>
    simp only [flush, List.forM_eq_forM, List.forM_cons] at *
    exact HistoryFrame.bind
      (HistoryFrame.bind (HistoryFrame.emit _ rfl) (fun _ =>
        (show HistoryFrame removedStamp (access _) from
          fun w h => focusPrefix_other Event.access accessEvent removedStamp (fun _ => rfl) _ w h).receiptObserved
          (fun _ => rfl)))
      (fun _ => ih)

theorem normalList_removed (g : Gro) : HistoryFrame removedStamp (normalList g) := by
  unfold normalList
  split
  · exact HistoryFrame.pure _ _
  · exact HistoryFrame.bind (flush_removed _) (fun _ => HistoryFrame.pure _ _)

theorem normalOne_removed (g : Gro) (e : Entry) (segs : Nat) : HistoryFrame removedStamp (normalOne g e segs) := by
  unfold normalOne
  dsimp only
  split
  · exact normalList_removed _
  · exact HistoryFrame.pure _ _

theorem receive_removed (g : Gro) (e : Entry) : HistoryFrame removedStamp (receive g e) := by
  unfold receive
  split
  · exact normalOne_removed _ _ _
  · split
    · exact HistoryFrame.bind (HistoryFrame.lift _ _) (fun _ => HistoryFrame.pure _ _)
    · exact HistoryFrame.pure _ _

theorem flushAll_removed (g : Gro) : HistoryFrame removedStamp (flushAll g) := by
  unfold flushAll
  apply HistoryFrame.bind
  · apply HistoryFrame.forIn
    intro e g
    exact HistoryFrame.bind (normalOne_removed _ _ _) (fun _ => HistoryFrame.pure _ _)
  · intro g
    exact HistoryFrame.bind (normalList_removed _) (fun _ => HistoryFrame.pure _ _)

theorem phase_receive (kind : PhaseKind) (g : Gro) (e : Entry) :
    PrefixPreserves (Phase kind) StampSafe (receive g e) :=
  phase_project kind _ _ _ (receive_access g e)
    (napiGroReceivePrefix_preserves stackFlushPrefix (fun _ _ hi => hi.safe) stackFlush_allocation _ _)
    (napiGroReceivePrefix_erases _ _ stackFlushPrefix_erases _ _)
    (RxRing.napiGroReceive_cell _ RxRing.stackForM_cell _ _)
    (receive_removed g e) (receive_appends g e)

theorem phase_flushAll (kind : PhaseKind) (g : Gro) :
    PrefixPreserves (Phase kind) StampSafe (flushAll g) :=
  phase_project kind _ _ id (flushAll_access g).to_mapped
    (napiGroFlushAllPrefix_preserves stackFlushPrefix (fun _ _ hi => hi.safe) stackFlush_allocation _)
    (napiGroFlushAllPrefix_erases _ _ stackFlushPrefix_erases _)
    (RxRing.napiGroFlushAll_cell _ RxRing.stackForM_cell _)
    (flushAll_removed g) (flushAll_appends g)

theorem phase_peek (kind : PhaseKind) (pid : PeerId) :
    PrefixPreserves (Phase kind) StampSafe (access (peekAccess pid)) := by
  apply phase_access kind _ (peekAccess_allocation pid) (peekAccess_erases pid)
  unfold peekRxQueue
  apply (RxRing.getPeer_cell pid).bind
  intro p
  apply (RxRing.kernel (prevQueuePeek_sameKernel p.rxQueue)).bind
  intro out
  exact (RxRing.getPeer_cell pid).bind (fun _ =>
    (RxRing.setPeer_frame pid _).bind (fun _ => SameView.pure _ _))

theorem phase_ready (kind : PhaseKind) (first : Option SkbId) :
    PrefixPreserves (Phase kind) StampSafe (access (readyAccess first)) := by
  apply phase_access kind _ (readyAccess_allocation first) (readyAccess_erases first)
  unfold WG.andM
  apply (RxRing.kernel (sameKernel_branch _ _)).bind
  intro go
  split
  · cases first with
    | none => exact RxRing.kernel (by intro w x v hr; cases hr)
    | some skb => exact (RxRing.getRx_frame skb).bind (fun _ => RxRing.kernel (sameKernel_branch _ _))
  · exact SameView.pure _ _

theorem phase_complete (kind : PhaseKind) (pid : PeerId) :
    PrefixPreserves (Phase kind) StampSafe (access (completeAccess pid)) := by
  apply phase_access kind _ (completeAccess_allocation pid) (completeAccess_erases pid)
  unfold completeRxQueue
  exact (RxRing.getPeer_cell pid).bind (fun _ => RxRing.setPeer_frame pid _)

theorem phase_option (kind : PhaseKind) (out : Option Entry) (g : Gro) :
    PrefixPreserves (Phase kind) StampSafe
      (forIn out.toList g (fun e g => do let g' ← receive g e; pure (.yield g'))) :=
  PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    (fun e g => PrefixPreserves.bind (phase_receive kind g e)
      (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.safe) _))

theorem phase_invariant (kind : PhaseKind) (why : String) (f : Unit → Obs α) :
    PrefixEnsures (Phase kind) StampSafe (liftPrefix (invariant why) >>= f) Q := by
  intro w h hi
  exact ⟨[], by change h = h ++ []; simp, hi.safe, True.intro⟩

theorem phase_unsupported (kind : PhaseKind) (why : String) (f : Unit → Obs α) :
    PrefixEnsures (Phase kind) StampSafe (liftPrefix (unsupported why) >>= f) Q := by
  intro w h hi
  exact ⟨[], by change h = h ++ []; simp, hi.safe, True.intro⟩

theorem phase_bind (kind : PhaseKind) (g : Obs α) (f : α → Obs β)
    (hg : PrefixPreserves (Phase kind) StampSafe g)
    (hf : ∀ x, PrefixEnsures (Phase kind) StampSafe (f x) Q) :
    PrefixEnsures (Phase kind) StampSafe (g >>= f) Q := PrefixEnsures.bind hg hf

macro "rx_stamp_step" : tactic => `(tactic|
  repeat' first
    | exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi)
    | with_reducible apply phase_invariant
    | with_reducible apply phase_unsupported
    | with_reducible apply PrefixEnsures.bind (phase_capture _)
    | with_reducible apply PrefixEnsures.bind (phase_drop _ _ _ _)
    | with_reducible apply PrefixEnsures.bind (phase_free _ _)
    | with_reducible apply phase_bind _ _ _ (phase_consume _ _ _ _ _ _ _)
    | with_reducible apply phase_bind _ _ _ (phase_option _ _ _)
    | with_reducible apply phase_bind _ _ _ (phase_flushAll _ _)
    | with_reducible apply phase_bind _ _ _ (phase_peek _ _)
    | with_reducible apply phase_bind _ _ _ (phase_ready _ _)
    | with_reducible apply phase_bind _ _ _ (phase_complete _ _)
    | with_reducible apply phase_bind _ _ _ (phase_access _ _
        (AmbientContracts.drop (counterValidatePrefix_spec allocationAmbient (fun _ => True) _ _))
        (counterValidatePrefix_erases _ _) (RxRing.counterValidate_cell _ _))
    | with_reducible apply phase_bind _ _ _ (phase_access _ _ (allocationTx.put _ _)
        (keypairPutPrefix_erases _ _) (RxRing.keypairPut_cell _ _))
    | with_reducible apply phase_bind _ _ _ (phase_access _ _ (allocationAmbient.peerPut _)
        (peerPutMixed_erases _) (RxRing.peerPut_cell _))
    | with_reducible apply phase_bind _ _ _ (phase_lift _ _ (sameKernel_branch _ _))
    | with_reducible apply phase_bind _ _ _ (phase_lift _ _ (endpointFromSkb_sameKernel _))
    | with_reducible apply PrefixEnsures.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split))

/-- Every reached removal has a distinct allocation stamp. A normal return
has observed an actual packet release for every removed stamp. Stops retain
only the prefix safety conclusion, so a failed callback may leave a pending stamp. -/
theorem poll_phase (pid : PeerId) (budget : Nat) :
    PrefixPreserves (Phase .ready) StampSafe (poll pid budget) := by
  unfold poll
  apply PrefixEnsures.bind (phase_lift .ready _ (sameKernel_branch _ _))
  intro noBudget
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi)
  · apply PrefixEnsures.bind (Q := fun _ => Phase .ready)
    · change PrefixPreserves (Phase .ready) StampSafe _
      apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
      intro index acc
      change PrefixEnsures (Phase .ready) StampSafe _ (fun _ => Phase .ready)
      rx_stamp_step
    · intro acc
      rx_stamp_step

/-- A fresh local metadata journal accepts any valid accumulated lifetime history. -/
theorem seed_ready (prior : List LifetimeEvent) (w : World)
    (hi : AllocationInv prior w) : Phase .ready (seed prior) w := by
  have hm : removedStamps (seed prior) = [] :=
    filterMap_disjoint Event.access removedStamp (fun _ => rfl) prior
  exact ⟨by simpa using hi, by rw [hm]; simp,
    fun _ hs => by rw [hm] at hs; contradiction⟩

/-- Per-poll removal identities are distinct on every reached prefix; all are
released on normal return. The initial lifetime history may be nonempty. -/
theorem poll_removed_stamps (pid : PeerId) (budget : Nat) (w : World)
    (prior : List LifetimeEvent) (hi : AllocationInv prior w) :
    (removedStamps (runPrefix (poll pid budget) w (seed prior)).2).Nodup ∧
      (match (runPrefix (poll pid budget) w (seed prior)).1 with
       | .error _ => True
       | .ok _ => ∀ s ∈ removedStamps (runPrefix (poll pid budget) w (seed prior)).2,
          Released (runPrefix (poll pid budget) w (seed prior)).2 s) := by
  obtain ⟨_, _, hs, hp⟩ := poll_phase pid budget w (seed prior) (seed_ready prior w hi)
  refine ⟨hs.2, ?_⟩
  cases hr : (runPrefix (poll pid budget) w (seed prior)).1 with
  | error _ => trivial
  | ok out => exact (show Phase .ready _ out.2 from by simpa only [hr] using hp).extra

abbrev EntryKey := Nat × SkbId × PacketStamp
def Entry.key (e : Entry) : EntryKey := (e.tag.occurrence, e.tag.skb, e.stamp)
def removedKey : Event → Option EntryKey | .removed n skb s => some (n, skb, s) | _ => none
def enteredEntry : Event → Option Entry | .entered e => some e | _ => none
def removalKeys (h : List Event) := h.filterMap removedKey
def entries (h : List Event) := h.filterMap enteredEntry
def Supported (h : List Event) := ∀ e ∈ entries h, e.key ∈ removalKeys h

structure Context (g : Gro) (extra : List EntryKey) (h : List Event) : Prop where
  entered : Supported h
  held : ∀ e ∈ g.rxList ++ g.held, e.key ∈ removalKeys h
  extra : ∀ k ∈ extra, k ∈ removalKeys h

theorem Context.weaken {g : Gro} {extra : List EntryKey} {h : List Event} (hi : Context g extra h) : Context g [] h :=
  ⟨hi.entered, hi.held, by simp⟩

theorem context_quiet (g : Gro) (extra : List EntryKey) (a : Obs α)
    (hr : HistoryFrame removedKey a) (he : HistoryFrame enteredEntry a) (ha : Appends a) :
    PrefixPreserves (fun h _ => Context g extra h) Supported a := by
  intro w h hi
  obtain ⟨tail, ht⟩ := ha w h
  have hc : Context g extra (runPrefix a w h).2 := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Supported, entries, removalKeys, hr w h, he w h] using hi.entered
    · simpa only [removalKeys, hr w h] using hi.held
    · simpa only [removalKeys, hr w h] using hi.extra
  refine ⟨tail, ht, hc.entered, ?_⟩
  cases (runPrefix a w h).1
  · trivial
  · exact hc

theorem context_bind (g : Gro) (extra : List EntryKey) (a : Obs α) (f : α → Obs β)
    (ha : PrefixPreserves (fun h _ => Context g extra h) Supported a)
    (hf : ∀ x, PrefixEnsures (fun h _ => Context g extra h) Supported (f x) Q) :
    PrefixEnsures (fun h _ => Context g extra h) Supported (a >>= f) Q :=
  PrefixEnsures.bind (Q := fun _ h _ => Context g extra h) ha hf

theorem context_access (g : Gro) (extra : List EntryKey) (a : MixedM α) :
    PrefixPreserves (fun h _ => Context g extra h) Supported (access a) :=
  context_quiet g extra _
    (fun w h => focusPrefix_other Event.access accessEvent removedKey (fun _ => rfl) a w h)
    (fun w h => focusPrefix_other Event.access accessEvent enteredEntry (fun _ => rfl) a w h)
    (access_appends a)

theorem context_lift (g : Gro) (extra : List EntryKey) (a : M α) :
    PrefixPreserves (fun h _ => Context g extra h) Supported (liftPrefix a) :=
  context_quiet g extra _ (HistoryFrame.lift _ _) (HistoryFrame.lift _ _) (Appends.lift _)

theorem context_capture (g : Gro) (extra : List EntryKey) (skb : SkbId) :
    PrefixPreserves (fun h _ => Context g extra h) Supported (capture skb) := by
  apply context_quiet g extra _ ?_ ?_ (capture_appends skb)
  all_goals
    intro w h
    rw [capture_run]
    cases (getRxSkb skb).run w <;> simp [List.filterMap_append, removedKey, enteredEntry]

theorem context_buffered (g : Gro) (extra : List EntryKey) (e : Entry) :
    PrefixPreserves (fun h _ => Context g extra h) Supported (emitPrefix (.buffered e)) :=
  context_quiet g extra _ (HistoryFrame.emit _ rfl) (HistoryFrame.emit _ rfl) (emit_appends _)

theorem context_mark (g : Gro) (n skb : Nat) (stamp : PacketStamp) :
    PrefixEnsures (fun h _ => Context g [] h) Supported (emitPrefix (.removed n skb stamp))
      (fun _ h _ => Context g [(n, skb, stamp)] h) := by
  intro w h hi
  have hr : removalKeys (h ++ [Event.removed n skb stamp]) = removalKeys h ++ [(n, skb, stamp)] := by
    simp [removalKeys, removedKey, List.filterMap_append]
  have he : entries (h ++ [Event.removed n skb stamp]) = entries h := by
    simp [entries, enteredEntry, List.filterMap_append]
  have hc : Context g [(n, skb, stamp)] (h ++ [.removed n skb stamp]) := by
    refine ⟨?_, ?_, ?_⟩
    · intro e hm
      rw [he] at hm
      rw [hr]; exact List.mem_append_left _ (hi.entered e hm)
    · intro e hm; rw [hr]; exact List.mem_append_left _ (hi.held e hm)
    · intro k hk; rw [hr]; exact List.mem_append_right _ hk
  exact ⟨[.removed n skb stamp], rfl, hc.entered, hc⟩

theorem context_drop (g : Gro) (pid n skb : Nat) (stamp : PacketStamp) :
    PrefixEnsures (fun h _ => Context g [] h) Supported (drop pid n skb stamp)
      (fun _ h _ => Context g [(n, skb, stamp)] h) := by
  unfold drop
  exact context_bind g [] _ _ (context_access g [] _) (fun _ => context_mark g n skb stamp)

theorem context_consume (g : Gro) (pid n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    PrefixEnsures (fun h _ => Context g [(n, skb, stamp)] h) Supported
      (consume pid n skb stamp pkt ep)
      (fun out h _ => Context g (out.toList.map Entry.key) h) := by
  unfold consume
  apply context_bind g [(n, skb, stamp)] _ _ (context_access g [(n, skb, stamp)] _)
  intro out
  cases out with
  | none => exact PrefixEnsures.pure (fun _ _ hi => hi.entered) (fun _ _ hi => hi.weaken)
  | some bytes =>
    apply context_bind g [(n, skb, stamp)] _ _ (context_buffered g [(n, skb, stamp)] _)
    intro _
    exact PrefixEnsures.pure (fun _ _ hi => hi.entered) (fun _ _ hi => hi)

theorem context_enter (g : Gro) (extra : List EntryKey) (e : Entry)
    (hin : e ∈ g.rxList ++ g.held) :
    PrefixPreserves (fun h _ => Context g extra h) Supported (enter e) := by
  unfold enter
  change PrefixEnsures (fun h _ => Context g extra h) Supported _ (fun _ h _ => Context g extra h)
  apply PrefixEnsures.bind (Q := fun _ h _ => Context g extra h)
  · intro w h hi
    have hr : removalKeys (h ++ [Event.entered e]) = removalKeys h := by
      simp [removalKeys, removedKey, List.filterMap_append]
    have he : entries (h ++ [Event.entered e]) = entries h ++ [e] := by
      simp [entries, enteredEntry, List.filterMap_append]
    have hc : Context g extra (h ++ [.entered e]) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x hm
        rw [he, List.mem_append, List.mem_singleton] at hm
        rw [hr]
        rcases hm with old | rfl
        · exact hi.entered x old
        · exact hi.held x hin
      · simpa only [hr] using hi.held
      · simpa only [hr] using hi.extra
    exact ⟨[.entered e], rfl, hc.entered, hc⟩
  · intro _
    exact context_quiet g extra _
      ((show HistoryFrame removedKey (access _) from
        fun w h => focusPrefix_other Event.access accessEvent removedKey (fun _ => rfl) _ w h).receiptObserved
        (fun _ => rfl))
      ((show HistoryFrame enteredEntry (access _) from
        fun w h => focusPrefix_other Event.access accessEvent enteredEntry (fun _ => rfl) _ w h).receiptObserved
        (fun _ => rfl))
      (access_appends _).receiptObserved

theorem context_flush (g : Gro) (extra : List EntryKey) (es : List Entry)
    (hin : ∀ e ∈ es, e ∈ g.rxList ++ g.held) :
    PrefixPreserves (fun h _ => Context g extra h) Supported (flush es) := by
  induction es with
  | nil => exact PrefixPreserves.pure (fun _ _ hi => hi.entered) _
  | cons e rest ih =>
    simp only [flush, List.forM_eq_forM, List.forM_cons] at *
    exact PrefixPreserves.bind (context_enter g extra e (hin e (by simp)))
      (fun _ => ih (fun x hx => hin x (by simp [hx])))

theorem context_normalList (g : Gro) (extra : List EntryKey) :
    PrefixEnsures (fun h _ => Context g extra h) Supported (normalList g)
      (fun out h _ => Context out extra h) := by
  unfold normalList
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.entered) (fun _ _ hi => hi)
  · apply context_bind g extra _ _ (context_flush g extra g.rxList (fun _ hx => List.mem_append_left _ hx))
    intro _
    apply PrefixEnsures.pure (fun _ _ hi => hi.entered)
    intro h w hi
    exact ⟨hi.entered, fun e he => hi.held e (List.mem_append_right _ (by simpa using he)), hi.extra⟩

theorem context_normalOne (g : Gro) (extra : List EntryKey) (e : Entry) (segs : Nat) :
    PrefixEnsures (fun h _ => Context g (e.key :: extra) h) Supported (normalOne g e segs)
      (fun out h _ => Context out extra h) := by
  have transfer (h : List Event) (hi : Context g (e.key :: extra) h) :
      Context {g with rxList := g.rxList ++ [e], rxCount := g.rxCount + segs} extra h := by
    refine ⟨hi.entered, ?_, fun k hk => hi.extra k (by simp [hk])⟩
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with (old | rfl) | held
    · exact hi.held x (List.mem_append_left _ old)
    · exact hi.extra x.key (by simp)
    · exact hi.held x (List.mem_append_right _ held)
  unfold normalOne
  dsimp only
  split
  · exact (context_normalList _ extra).consequence (fun _ _ hi => transfer _ hi) (fun _ _ _ hi => hi)
  · exact PrefixEnsures.pure (fun _ _ hi => hi.entered) (fun _ _ hi => transfer _ hi)

theorem context_receive (g : Gro) (extra : List EntryKey) (e : Entry) :
    PrefixEnsures (fun h _ => Context g (e.key :: extra) h) Supported (receive g e)
      (fun out h _ => Context out extra h) := by
  have transfer (h : List Event) (hi : Context g (e.key :: extra) h) :
      Context {g with held := g.held ++ [e]} extra h := by
    refine ⟨hi.entered, ?_, fun k hk => hi.extra k (by simp [hk])⟩
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with old | held | rfl
    · exact hi.held x (List.mem_append_left _ old)
    · exact hi.held x (List.mem_append_right _ held)
    · exact hi.extra x.key (by simp)
  unfold receive
  split
  · exact context_normalOne g extra e 1
  · split
    · apply context_bind g (e.key :: extra) _ _ (context_lift _ _ _)
      intro _
      exact PrefixEnsures.pure (fun _ _ hi => hi.entered) (fun _ _ hi => transfer _ hi)
    · exact PrefixEnsures.pure (fun _ _ hi => hi.entered) (fun _ _ hi => transfer _ hi)

theorem context_option (g : Gro) (out : Option Entry) :
    PrefixEnsures (fun h _ => Context g (out.toList.map Entry.key) h) Supported
      (forIn out.toList g (fun e g => do let g' ← receive g e; pure (.yield g')))
      (fun out h _ => Context out [] h) := by
  cases out with
  | none => exact PrefixEnsures.pure (fun _ _ hi => hi.entered) (fun _ _ hi => hi)
  | some e =>
    simpa only [Option.toList_some, List.forIn_cons, List.forIn_nil, bind_assoc,
      pure_bind, bind_pure, List.map_cons, List.map_nil] using context_receive g [] e

theorem context_forIn (xs : List Entry) (g : Gro) (extra : List EntryKey)
    (f : Entry → Gro → Obs (ForInStep Gro))
    (hf : ∀ e ∈ xs, ∀ g, PrefixEnsures (fun h _ => Context g extra h) Supported
      (f e g) (fun out h _ => Context out.value extra h)) :
    PrefixEnsures (fun h _ => Context g extra h) Supported (forIn xs g f)
      (fun out h _ => Context out extra h) := by
  induction xs generalizing g with
  | nil => exact PrefixEnsures.pure (fun _ _ hi => hi.entered) (fun _ _ hi => hi)
  | cons e rest ih =>
    rw [List.forIn_cons]
    apply PrefixEnsures.bind (hf e (by simp) g)
    intro step
    cases step with
    | done g => exact PrefixEnsures.pure (fun _ _ hi => hi.entered) (fun _ _ hi => hi)
    | yield g => exact ih g (fun e he g => hf e (by simp [he]) g)

theorem context_flushAll (g : Gro) :
    PrefixEnsures (fun h _ => Context g [] h) Supported (flushAll g)
      (fun _ h _ => Supported h) := by
  unfold flushAll
  apply PrefixEnsures.bind (Q := fun out h _ => Context out (g.held.map Entry.key) h)
  · apply PrefixEnsures.consequence
    · apply context_forIn g.held g (g.held.map Entry.key)
      intro e he cur
      apply PrefixEnsures.bind (Q := fun out h _ => Context out (g.held.map Entry.key) h)
      · apply (context_normalOne cur (g.held.map Entry.key) e 1).consequence
        · intro h w hi
          refine ⟨hi.entered, hi.held, ?_⟩
          intro k hk
          simp only [List.mem_cons] at hk
          rcases hk with rfl | old
          · exact hi.extra e.key (List.mem_map.mpr ⟨e, he, rfl⟩)
          · exact hi.extra k old
        · intro _ _ _ hi; exact hi
      · intro out
        exact PrefixEnsures.pure (fun _ _ hi => hi.entered) (fun _ _ hi => hi)
    · intro h w hi
      refine ⟨hi.entered, hi.held, ?_⟩
      intro k hk
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
      exact hi.held e (List.mem_append_right _ he)
    · intro _ _ _ hi; exact hi
  · intro cur
    apply PrefixEnsures.bind (Q := fun out h _ => Context out (g.held.map Entry.key) h)
    · apply (context_normalList {cur with held := []} (g.held.map Entry.key)).consequence
      · intro h w hi
        exact ⟨hi.entered, fun e he => hi.held e (List.mem_append_left _ (by simpa using he)), hi.extra⟩
      · intro _ _ _ hi; exact hi
    · intro _
      exact PrefixEnsures.pure (fun _ _ hi => hi.entered) (fun _ _ hi => hi.entered)

theorem context_invariant (g : Gro) (extra : List EntryKey) (why : String) (f : Unit → Obs α) :
    PrefixEnsures (fun h _ => Context g extra h) Supported (liftPrefix (invariant why) >>= f) Q := by
  intro w h hi
  exact ⟨[], by change h = h ++ []; simp, hi.entered, True.intro⟩

theorem context_unsupported (g : Gro) (extra : List EntryKey) (why : String) (f : Unit → Obs α) :
    PrefixEnsures (fun h _ => Context g extra h) Supported (liftPrefix (unsupported why) >>= f) Q := by
  intro w h hi
  exact ⟨[], by change h = h ++ []; simp, hi.entered, True.intro⟩

macro "rx_support_step" : tactic => `(tactic|
  repeat' first
    | exact PrefixEnsures.pure (fun _ _ hi => hi.entered) (fun _ _ hi => hi.weaken)
    | exact PrefixEnsures.pure (fun _ _ hi => hi.entered) (fun _ _ hi => hi.entered)
    | exact PrefixEnsures.pure (fun _ _ hi => hi) (fun _ _ hi => hi)
    | with_reducible apply context_invariant
    | with_reducible apply context_unsupported
    | with_reducible apply PrefixEnsures.bind (context_drop _ _ _ _ _)
    | with_reducible apply PrefixEnsures.bind (context_consume _ _ _ _ _ _ _)
    | with_reducible apply PrefixEnsures.bind (context_option _ _)
    | with_reducible apply PrefixEnsures.bind (context_flushAll _)
    | with_reducible apply context_bind _ _ _ _ (context_capture _ _ _)
    | with_reducible apply context_bind _ _ _ _ (context_access _ _ _)
    | with_reducible apply context_bind _ _ _ _ (context_lift _ _ _)
    | with_reducible apply PrefixEnsures.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split))

/-- Every entered stamped payload comes from an actual removal in this same
poll journal. This relation retains the whole occurrence/slot/stamp triple. -/
theorem poll_supported (pid : PeerId) (budget : Nat) :
    PrefixEnsures (fun h _ => Context {} [] h) Supported (poll pid budget)
      (fun _ h _ => Supported h) := by
  unfold poll
  apply context_bind {} [] _ _ (context_lift _ _ _)
  intro noBudget
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.entered) (fun _ _ hi => hi.entered)
  · apply PrefixEnsures.bind (Q := fun acc : Nat × Gro × Bool => fun h _ => Context acc.2.1 [] h)
    · with_reducible apply (PrefixEnsures.rangeInvariant _ (0, ({} : Gro), false) _
        (fun acc : Nat × Gro × Bool => fun h _ => Context acc.2.1 [] h) Supported
        (fun _ _ _ hi => hi.entered))
      intro index acc
      rx_support_step
    · intro acc
      rx_support_step

theorem seed_context (prior : List LifetimeEvent) : Context {} [] (seed prior) := by
  have he : entries (seed prior) = [] :=
    filterMap_disjoint Event.access enteredEntry (fun _ => rfl) prior
  refine ⟨?_, by simp, by simp⟩
  intro e hm
  rw [he] at hm
  contradiction

/-- Full callback provenance is proved on the stamped journal itself, without
recovering stamp agreement from two independently erased observations. -/
theorem poll_entry_support (pid : PeerId) (budget : Nat) (w : World) (prior : List LifetimeEvent) :
    Supported (runPrefix (poll pid budget) w (seed prior)).2 :=
  (poll_supported pid budget w (seed prior) (seed_context prior)).choose_spec.2.1

theorem removalKeys_stamps (h : List Event) :
    (removalKeys h).map (fun k => k.2.2) = removedStamps h := by
  induction h with
  | nil => rfl
  | cons e rest ih => cases e <;>
      simp [removalKeys, removedStamps, removedKey, removedStamp] at * <;> exact ih

theorem entries_tags (h : List Event) :
    (entries h).map Entry.tag = enteredEntries (h.filterMap groEvent) := by
  induction h with
  | nil => rfl
  | cons e rest ih => cases e <;>
      simp [entries, enteredEntry, enteredEntries, groEvent] at * <;> exact ih

/-- This elementary list fact follows the proof used for routing entries,
without importing that independent proof layer. -/
theorem key_eq_of_nodup_map {α β : Type} {f : α → β} {xs : List α}
    (hn : (xs.map f).Nodup) {x y : α} (hx : x ∈ xs) (hy : y ∈ xs)
    (he : f x = f y) : x = y := by
  induction xs with
  | nil => simp at hx
  | cons z zs ih =>
      have hd := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hx with hx | hx
      · subst x
        rcases List.mem_cons.mp hy with hy | hy
        · exact hy.symm
        · exact False.elim (hd.1 (List.mem_map.mpr ⟨y, hy, he.symm⟩))
      · rcases List.mem_cons.mp hy with hy | hy
        · subst y
          exact False.elim (hd.1 (List.mem_map.mpr ⟨x, hx, he⟩))
        · exact ih hd.2 hx hy

theorem supported_distinct (h : List Event) (hs : Supported h)
    (hr : (removedStamps h).Nodup)
    (ho : ((entries h).map (fun e => e.tag.occurrence)).Nodup) :
    ((entries h).map Entry.stamp).Nodup := by
  have hd : ((removalKeys h).map (fun k => k.2.2)).Nodup := by
    rw [removalKeys_stamps]; exact hr
  change List.Pairwise (fun a b => a ≠ b) _ at ho ⊢
  rw [List.pairwise_map] at ho ⊢
  apply ho.imp_of_mem
  intro a b ha hb hn he
  have hk : a.key = b.key := key_eq_of_nodup_map hd (hs a ha) (hs b hb) he
  exact hn (congrArg Prod.fst hk)

theorem supported_stamp_mem (h : List Event) (hs : Supported h) (e : Entry)
    (he : e ∈ entries h) : e.stamp ∈ removedStamps h := by
  rw [← removalKeys_stamps]
  exact List.mem_map.mpr ⟨e.key, hs e he, rfl⟩

/-- Callback entry allocation stamps are distinct in every reached prefix of
one poll. Normal poll return has released every entered stamp, including GRO
payloads whose packet storage was freed before their later callback. -/
theorem poll_entry_stamps (pid : PeerId) (budget : Nat) (w : World)
    (prior : List LifetimeEvent) (hi : AllocationInv prior w) :
    let h := (runPrefix (poll pid budget) w (seed prior)).2
    ((entries h).map Entry.stamp).Nodup ∧
      (match (runPrefix (poll pid budget) w (seed prior)).1 with
       | .error _ => True
       | .ok _ => ∀ e ∈ entries h, Released h e.stamp) := by
  dsimp only
  have hs := poll_entry_support pid budget w prior
  have hr := poll_removed_stamps pid budget w prior hi
  have ho := (poll_callback_tags pid budget w prior).1
  rw [← entries_tags, List.map_map] at ho
  refine ⟨supported_distinct _ hs hr.1 ho, ?_⟩
  cases he : (runPrefix (poll pid budget) w (seed prior)).1 with
  | error e => trivial
  | ok out =>
    have hp := hr.2
    simp only [he] at hp
    exact fun e hm => hp e.stamp (supported_stamp_mem _ hs e hm)

end Leanux.Proofs.WG.Queues.RxJoint
