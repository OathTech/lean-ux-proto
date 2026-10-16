import Leanux.Proofs.Logged.FocusComposition
import Leanux.Proofs.WG.Queues.RxPollHistory

/-! Cross-poll identity composition at normal call boundaries. Failed prefixes
retain audit safety and callback-entry uniqueness, but need not release their
last captured packet. Focused audit calls preserve recorded metadata; that frame
does not certify coverage of any polls hidden inside such a call. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

structure BoundaryInv (h : List Event) (w : World) : Prop where
  audit : AuditInv (auditHistory h) w
  distinct : (stamps h).Nodup
  released : ∀ s ∈ stamps h, Released h s

def BoundarySafe (h : List Event) := AuditSafe (auditHistory h) ∧ (stamps h).Nodup

theorem BoundaryInv.safe (hi : BoundaryInv h w) : BoundarySafe h :=
  ⟨hi.audit.safe, hi.distinct⟩

theorem boundary_initial (w : World) (hi : AllocationInv [] w.wg) : BoundaryInv [] w :=
  ⟨audit_initial hi, by simp [stamps, entries], by simp [stamps, entries]⟩

theorem released_promote (suffix : List RxJoint.Event) (s : PacketStamp) :
    Released (suffix.map promote) s ↔ RxJoint.Released suffix s := by
  simp only [Released, promote_prior, RxJoint.PriorReleased, RxJoint.Released]

/-- A fresh local poll adds stamps disjoint from all previously completed
entries. Success restores the release boundary; Stops keep uniqueness only. -/
theorem observePoll_preserves (pid : PeerId) (budget : Nat) :
    PrefixPreserves BoundaryInv BoundarySafe (observePoll pid budget) := by
  intro w h hi
  have allocation : AllocationInv (prior h) w.wg := hi.audit.1
  obtain ⟨suffix, hs⟩ := RxJoint.poll_appends pid budget w (RxJoint.seed (prior h))
  have hg := observePoll_suffix pid budget w h _ suffix (Prod.ext rfl hs)
  have ha := (observePoll_projects pid budget).preserves
    (auditFocus_preserves
      (rxPollStackPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) (ProductTxContracts.ofNative allocationTx) ⟨fun len => (allocationRx.stats len).liftWGObserver, fun why => (allocationRx.dishonest why).liftWGObserver, fun id => (allocationRx.free id).liftWGObserver⟩ ⟨fun P => (allocationWgXmit.errors P).liftWGObserver⟩ pid budget))
    w h hi.audit
  have perPoll := RxJoint.poll_suffix_entries pid budget w (prior h) allocation suffix hs
  have fresh := (RxJoint.poll_suffix_fresh pid budget w (prior h) allocation suffix hs).2
  have hd : (stamps (h ++ suffix.map promote)).Nodup := by
    rw [stamps_append]
    change (stamps h ++ (entries (suffix.map promote)).map RxJoint.Entry.stamp).Nodup
    rw [promote_entries]
    apply List.nodup_append.mpr
    refine ⟨hi.distinct, perPoll.1, ?_⟩
    intro a ha b hb eq
    subst b
    obtain ⟨e, he, hstamp⟩ := List.mem_map.mp hb
    apply fresh e he
    rw [hstamp]
    exact hi.released a ha
  refine ⟨suffix.map promote, by rw [hg], ?_, ?_⟩
  · exact ⟨ha.1, by simpa only [hg] using hd⟩
  · rw [hg]
    cases hr : (runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (prior h))).1 with
    | error e => trivial
    | ok out =>
      have auditOut : AuditInv (auditHistory (h ++ suffix.map promote)) out.2 := by
        simpa only [hg, hr, auditHistory] using ha.2
      have rel : ∀ e ∈ RxJoint.entries suffix, RxJoint.Released suffix e.stamp := by
        simpa only [hr] using perPoll.2
      refine ⟨auditOut, hd, ?_⟩
      intro s hm
      rw [stamps_append, List.mem_append] at hm
      apply (released_append _ _ _).mpr
      rcases hm with old | new
      · exact Or.inl (hi.released s old)
      · change s ∈ (entries (suffix.map promote)).map RxJoint.Entry.stamp at new
        rw [promote_entries] at new
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp new
        exact Or.inr ((released_promote suffix e.stamp).mpr (rel e he))

/-- An existing audit observer preserves entry metadata and the completed-poll
boundary. This is a frame for recorded entries, not a claim that its source
contains no poll or that hidden callback entries have been observed. -/
theorem audit_preserves (a : AuditM α) (ha : PrefixPreserves AuditInv AuditSafe a) :
    PrefixPreserves BoundaryInv BoundarySafe (audit a) := by
  intro w h hi
  obtain ⟨suffix, hs⟩ := Appends.focus Event.audit auditEvent a w h
  change (runPrefix (audit a) w h).2 = h ++ suffix at hs
  have hp := (audit_projects ha).preserves ha w h hi.audit
  have he : stamps (runPrefix (audit a) w h).2 = stamps h :=
    congrArg (List.map RxJoint.Entry.stamp) (audit_entries a w h)
  refine ⟨suffix, hs, ⟨hp.1, he ▸ hi.distinct⟩, ?_⟩
  cases hr : (runPrefix (audit a) w h).1 with
  | error e => trivial
  | ok out =>
    refine ⟨by simpa only [hr, auditHistory] using hp.2, he ▸ hi.distinct, ?_⟩
    intro s hm
    have old := hi.released s (he ▸ hm)
    rw [hs]
    exact (released_append h suffix s).mpr (Or.inl old)

def mixed (a : PrefixM LifetimeEvent α) : Obs α := audit (auditFocus a)

theorem mixed_erases (he : ErasesPrefix a original) : ErasesPrefix (mixed a) original :=
  audit_erases (auditFocus_erases he)

theorem mixed_preserves (ha : PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe a) :
    PrefixPreserves BoundaryInv BoundarySafe (mixed a) :=
  audit_preserves _ (auditFocus_preserves ha)

theorem mixed_projects (ha : PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe a) :
    ProjectsUnder AuditInv auditEvent (mixed a) (auditFocus a) :=
  audit_projects (auditFocus_preserves ha)

/-- Compose directly to one focused lifetime observer at the current audit
history, retaining probe interleaving and the continuation's actual prefix. -/
theorem projectsFocus_bind
    (hg : ProjectsUnder AuditInv auditEvent g (auditFocus a))
    (ha : PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe a)
    (hf : ∀ x, ProjectsUnder AuditInv auditEvent (f x) (auditFocus (b x)))
    (hb : ∀ x, PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe (b x)) :
    ProjectsUnder AuditInv auditEvent (g >>= f) (auditFocus (a >>= b)) := by
  have projected := projectsUnder_bind hg (auditFocus_preserves ha) hf
  have focused := FocusesUnder.bind (encode := AuditEvent.lifetime) (decode := AuditEvent.lifetime?)
    (fun _ => rfl) (FocusesUnder.focus a) ha (fun x => FocusesUnder.focus (b x)) hb
  intro w h hi
  exact (focused w (h.filterMap auditEvent) hi.1).symm.trans (projected w h hi)

theorem projectsFocus_lift (a : Leanux.M α) :
    ProjectsUnder AuditInv auditEvent (liftPrefix a) (auditFocus (liftPrefix a)) := by
  intro w h hi
  have focused := FocusesUnder.lift (I := fun h (w : World) => AllocationInv h w.wg)
    (encode := AuditEvent.lifetime) (decode := AuditEvent.lifetime?) a w (h.filterMap auditEvent) hi.1
  exact focused.symm.trans (projectsUnder_lift (I := AuditInv) auditEvent a w h hi)

theorem projectsFocus_pure (x : α) :
    ProjectsUnder AuditInv auditEvent (pure x) (auditFocus (pure x)) := by
  intro w h hi
  have focused := FocusesUnder.pure (I := fun h (w : World) => AllocationInv h w.wg)
    (encode := AuditEvent.lifetime) (decode := AuditEvent.lifetime?) x w (h.filterMap auditEvent) hi.1
  exact focused.symm.trans (projectsUnder_pure (I := AuditInv) auditEvent x w h hi)

/-- A finite actual sequence of observed polls inherits distinct allocation
stamps, even when its last poll stops inside a callback. This sequence is not
the scheduler/Runner caller spine. -/
def polls (calls : List (PeerId × Nat)) : Obs Unit :=
  calls.forM fun (pid, budget) => do discard <| observePoll pid budget

theorem polls_preserves (calls : List (PeerId × Nat)) :
    PrefixPreserves BoundaryInv BoundarySafe (polls calls) := by
  unfold polls
  apply PrefixPreserves.forM _ _ (fun _ _ hi => hi.safe)
  intro call
  exact PrefixPreserves.bind (observePoll_preserves call.1 call.2)
    (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.safe) ())

theorem polls_erases (calls : List (PeerId × Nat)) :
    ErasesPrefix (polls calls)
      (calls.forM fun (pid, budget) => do
        discard <| rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) := by
  unfold polls
  apply erasesPrefix_forM
  intro call
  exact erasesPrefix_bind (observePoll_erases call.1 call.2) (fun _ => erasesPrefix_pure ())

/-- Empty metadata accepts any allocation-valid World. The conclusion includes
every failed prefix; no assertion of completed stack delivery is made. -/
theorem polls_safe (calls : List (PeerId × Nat)) (w : World)
    (hi : AllocationInv [] w.wg) : BoundarySafe (runPrefix (polls calls) w []).2 :=
  (polls_preserves calls w [] (boundary_initial w hi)).choose_spec.2.1

end Leanux.Proofs.WG.Queues.RxHistory
