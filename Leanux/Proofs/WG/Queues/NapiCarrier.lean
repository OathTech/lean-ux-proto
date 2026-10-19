import Leanux.Proofs.WG.Queues.RxPollBoundary
import Leanux.Proofs.WG.Queues.DecryptIteration

/-! A fixed incoming history marks the accounting boundary. Only removal
records appended after that boundary subtract from its supplied carrier ledger.
The existing committed observer and its arbitrary prior history are unchanged. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.NapiCarrier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

def removed : RxHistory.Event → Option Packet
  | .removed _ _ stamp => some (PollCarrier.packetOfStamp stamp)
  | _ => none

def removedPackets (h : List RxHistory.Event) := h.filterMap removed

def At (initial : Ledger) (loans : Reservations) (before h : List RxHistory.Event) (w : World) : Prop :=
  ∃ suffix, h = before ++ suffix ∧
    DecryptIteration.Stable (remaining initial (removedPackets suffix)) loans w

theorem at_start (hi : DecryptIteration.Stable cs loans w) (h : List RxHistory.Event) :
    At cs loans h h w := by
  refine ⟨[],by simp,?_⟩
  have empty : remaining cs [] = cs := List.filter_eq_self.mpr (fun _ _ => rfl)
  simpa only [removedPackets,List.filterMap_nil,empty] using hi

theorem promote_removed (h : List RxJoint.Event) :
    removedPackets (h.map RxHistory.promote) = PollCarrier.removedPackets h := by
  unfold removedPackets PollCarrier.removedPackets RxJoint.removedStamps
  induction h with
  | nil => rfl
  | cons e h ih =>
    cases e <;> simp only [List.map_cons,List.filterMap_cons,RxHistory.promote,
      removed,RxJoint.removedStamp,List.map_cons,ih]

theorem normal_spec {α : Type} {a : RxHistory.Obs α}
    {P : List RxHistory.Event → World → Prop}
    {Q : α → List RxHistory.Event → World → Prop} (ha : Appends a)
    (hq : ∀ w h x v, P h w → (runPrefix a w h).1 = .ok (x,v) → Q x (runPrefix a w h).2 v) :
    PrefixEnsures P (fun _ => True) a Q := by
  intro w h hi
  obtain ⟨s,hs⟩ := ha w h
  refine ⟨s,hs,True.intro,?_⟩
  cases hr : (runPrefix a w h).1 with
  | error e => trivial
  | ok out => exact hq w h out.1 out.2 hi hr

/-- Each real poll subtracts exactly its promoted fresh removal suffix. The
ledger from earlier polls is retained through the same fixed history cut. -/
theorem observePoll_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (pid budget : Nat) :
    PrefixPreserves (At initial loans before) (fun _ => True) (RxHistory.observePoll pid budget) := by
  apply normal_spec (RxHistory.observePoll_appends pid budget)
  intro w h n v hi hr
  obtain ⟨old,history,hstable⟩ := hi
  obtain ⟨fresh,hfresh⟩ := RxJoint.poll_appends pid budget w (RxJoint.seed (RxHistory.prior h))
  have global := RxHistory.observePoll_suffix pid budget w h _ fresh (Prod.ext rfl hfresh)
  have original := (RxHistory.observePoll_erases pid budget w h).symm.trans hr
  have post := poll_normal_stable pid budget w v n
    (remaining initial (removedPackets old)) loans (RxHistory.prior h) hstable.1 hstable.2 original
  have freshRemoved : PollCarrier.removedPackets
      (runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior h))).2 =
      PollCarrier.removedPackets fresh := by
    rw [hfresh]
    simp only [PollCarrier.removedPackets,RxJoint.removedStamps,List.filterMap_append,List.map_append]
    change PollCarrier.removedPackets (RxJoint.seed _) ++ _ = _
    rw [PollCarrier.seed_removedPackets,List.nil_append]
  refine ⟨old ++ fresh.map RxHistory.promote,?_,?_⟩
  · rw [global]
    simp only [history,List.append_assoc]
  · simp only [removedPackets,List.filterMap_append]
    change DecryptIteration.Stable (remaining initial (removedPackets old ++ removedPackets (fresh.map RxHistory.promote))) loans v
    rw [promote_removed,remaining_append]
    simpa only [freshRemoved,DecryptIteration.Stable] using And.intro post.1 post.2.1

theorem store (hi : At initial loans before h w)
    (same : productStoreView v = productStoreView w) : At initial loans before h v := by
  obtain ⟨suffix,history,hstable⟩ := hi
  have wg : wgStoreView v.wg = wgStoreView w.wg := congrArg (fun p : ProductStore43 => p.2.2.2) same
  refine ⟨suffix,history,hstable.1.kernel wg,?_⟩
  apply hstable.2.view
  have dev : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev wg
  unfold stableView RxRing.nativeCell rxView
  rw [dev]

/-- Frames may append audit records, but they cannot erase an existing carrier
unless their actual appended suffix contains a removal record. -/
theorem frame_preserves (a : RxHistory.Obs α) (original : Leanux.M β) (project : α → β)
    (ha : Appends a) (erase : ErasesTo project a original)
    (same : SameProductStore original)
    (hist : ∀ w h, removedPackets (runPrefix a w h).2 = removedPackets h) :
    PrefixPreserves (At initial loans before) (fun _ => True) a := by
  apply normal_spec ha
  intro w h x v hi hr
  obtain ⟨old,history,stable⟩ := hi
  obtain ⟨extra,histExtra⟩ := ha w h
  have empty : removedPackets extra = [] := by
    have eq := hist w h
    rw [histExtra] at eq
    exact List.append_cancel_left (by simpa only [removedPackets,List.filterMap_append,List.append_nil] using eq)
  have run : original.run w = .ok (project x,v) := by rw [←erase w h,hr]; rfl
  have kept := store (initial := initial) (loans := loans) (before := before)
    ⟨old,history,stable⟩ ((ProjectedAction.iff_run _ _ _).mp same w (project x) v run)
  obtain ⟨old',history',stable'⟩ := kept
  refine ⟨old' ++ extra,by rw [histExtra,history',List.append_assoc],?_⟩
  simp only [removedPackets,List.filterMap_append]
  change DecryptIteration.Stable (remaining initial (removedPackets old' ++ removedPackets extra)) loans v
  rw [empty,List.append_nil]
  exact stable'

theorem audit_frame (a : AuditM α) (original : Leanux.M α)
    (erase : ErasesPrefix a original) (same : SameProductStore original) :
    PrefixPreserves (At initial loans before) (fun _ => True) (RxHistory.audit a) :=
  frame_preserves _ _ id (Appends.focus _ _ _) (RxHistory.audit_erases erase).to_projected same
    (fun w h => focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent removed (fun _ => rfl) a w h)

private theorem pending_store : SameProductStore (liftWG RxNapi.pendingSource) := by
  apply liftWG_sameProductStore
  unfold RxNapi.pendingSource
  exact getDev_sameWGStore.bind (fun d => SameView.pure _ _)

private theorem scheduled_store : SameProductStore (liftWG RxNapi.scheduledSource) := by
  apply liftWG_sameProductStore
  unfold RxNapi.scheduledSource
  exact getDev_sameWGStore.bind (fun d => SameView.pure _ _)

theorem softirq_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (At initial loans before) (fun _ => True) RxHistory.napiSoftirq := by
  unfold RxHistory.napiSoftirq
  apply RxNapi.softirq_preserves (I := At initial loans before) (fun _ _ _ => True.intro) (fun _ _ _ he hi => store hi he)
  · exact audit_frame _ _ (auditFocus_erases (liftWGObserver_erases RxNapi.pending_erases)) pending_store
  · exact observePoll_preserves initial loans before

theorem inline_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (At initial loans before) (fun _ => True) RxHistory.pollScheduledInline := by
  unfold RxHistory.pollScheduledInline
  apply RxNapi.inline_preserves (I := At initial loans before) (fun _ _ _ => True.intro) (fun _ _ _ he hi => store hi he)
  · exact audit_frame _ _ (auditFocus_erases (liftWGObserver_erases RxNapi.pending_erases)) pending_store
  · exact observePoll_preserves initial loans before

theorem irq_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (At initial loans before) (fun _ => True) RxHistory.napiIrqExit := by
  unfold RxHistory.napiIrqExit
  apply RxNapi.irqExit_preserves (I := At initial loans before) (fun _ _ _ => True.intro) (fun _ _ _ he hi => store hi he)
  · exact audit_frame _ _ (auditFocus_erases (liftWGObserver_erases RxNapi.scheduled_erases)) scheduled_store
  · exact softirq_preserves initial loans before

def Removed (cs : Ledger) (h : DecryptIteration.Journal) (_ : World)
    (ds : Ledger) (k : DecryptIteration.Journal) (_ : World) : Prop :=
  ∃ suffix, k = h ++ suffix ∧ ds = remaining cs (removedPackets suffix)

theorem advances (a : RxHistory.Obs Unit)
    (ha : ∀ initial loans before, PrefixPreserves (At initial loans before) (fun _ => True) a) :
    DecryptIteration.Advances a Removed := by
  intro cs loans w h v k hi hr
  have post := (ha cs loans h w h (at_start hi h)).choose_spec.2.2
  rw [hr] at post
  obtain ⟨suffix,history,stable⟩ := post
  exact ⟨_,⟨suffix,history,rfl⟩,stable⟩

theorem softirq_advances : DecryptIteration.Advances RxHistory.napiSoftirq Removed :=
  advances _ softirq_preserves

theorem irq_advances : DecryptIteration.Advances RxHistory.napiIrqExit Removed :=
  advances _ irq_preserves

end Leanux.Proofs.WG.Queues.RxCredits.NapiCarrier
