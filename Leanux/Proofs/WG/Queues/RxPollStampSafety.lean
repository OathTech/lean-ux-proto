import Leanux.Proofs.WG.Queues.RxPollJointProjection
import Leanux.Proofs.WG.Queues.RxPollProvenance

/-! Local identity cuts and fresh-journal composition. Prior lifetime history
is retained, while each poll starts its GRO occurrence journal at zero. These
cuts feed the whole-poll phase and stamped provenance contracts in
`RxPollStampPhase`; callback entry itself remains distinct from completion. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def seed (prior : List LifetimeEvent) : List Event := prior.map Event.access

@[simp] theorem seed_access (prior : List LifetimeEvent) :
    (seed prior).filterMap accessEvent = prior :=
  filterMap_encoded Event.access accessEvent (fun _ => rfl) prior

@[simp] theorem seed_gro (prior : List LifetimeEvent) :
    (seed prior).filterMap groEvent = [] :=
  filterMap_disjoint Event.access groEvent (fun _ => rfl) prior

theorem access_appends (a : MixedM α) : Appends (access a) := Appends.focus _ _ _

theorem emit_appends (e : Event) : Appends (emitPrefix e) := fun _ _ => ⟨[e], rfl⟩

theorem capture_appends (skb : SkbId) : Appends (capture skb) := by
  intro w h
  rw [capture_run]
  cases (getRxSkb skb).run w with
  | error e => exact ⟨[], by simp⟩
  | ok out => exact ⟨_, rfl⟩

theorem flush_appends (entries : List Entry) : Appends (flush entries) := by
  induction entries with
  | nil => exact Appends.pure _
  | cons e rest ih =>
    simp only [flush, List.forM_eq_forM, List.forM_cons] at *
    exact Appends.bind (Appends.bind (emit_appends _) (fun _ => Appends.focus _ _ _)) (fun _ => ih)

theorem normalList_appends (g : Gro) : Appends (normalList g) := by
  unfold normalList
  split
  · exact Appends.pure _
  · exact Appends.bind (flush_appends _) (fun _ => Appends.pure _)

theorem normalOne_appends (g : Gro) (e : Entry) (segs : Nat) : Appends (normalOne g e segs) := by
  unfold normalOne
  dsimp only
  split
  · exact normalList_appends _
  · exact Appends.pure _

theorem receive_appends (g : Gro) (e : Entry) : Appends (receive g e) := by
  unfold receive
  split
  · exact normalOne_appends _ _ _
  · split
    · exact Appends.bind (Appends.lift _) (fun _ => Appends.pure _)
    · exact Appends.pure _

theorem flushAll_appends (g : Gro) : Appends (flushAll g) := by
  unfold flushAll
  apply Appends.bind
  · apply Appends.forIn
    intro e g
    exact Appends.bind (normalOne_appends _ _ _) (fun _ => Appends.pure _)
  · intro g
    exact Appends.bind (normalList_appends _) (fun _ => Appends.pure _)

theorem consume_appends (pid occurrence skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    Appends (consume pid occurrence skb stamp pkt ep) := by
  unfold consume
  apply Appends.bind (Appends.focus _ _ _)
  intro out
  cases out with
  | none => exact Appends.pure _
  | some bytes => exact Appends.bind (emit_appends _) (fun _ => Appends.pure _)

theorem poll_appends (pid : PeerId) (budget : Nat) : Appends (poll pid budget) := by
  unfold poll drop
  repeat' first
    | with_reducible exact capture_appends _
    | with_reducible exact consume_appends _ _ _ _ _ _
    | with_reducible exact receive_appends _ _
    | with_reducible exact flushAll_appends _
    | with_reducible exact access_appends _
    | with_reducible exact emit_appends _
    | with_reducible exact Appends.lift _
    | with_reducible exact Appends.pure _
    | with_reducible apply Appends.range
    | with_reducible apply Appends.forIn
    | with_reducible apply Appends.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

/-- The fresh per-poll GRO journal is exact even with a nonempty earlier
lifetime history. No local ordinal is compared with a previous poll's ordinal. -/
theorem poll_fresh_gro (pid : PeerId) (budget : Nat) (w : World) (prior : List LifetimeEvent) :
    runPrefix (rxPollGro pid budget) w [] =
      ((runPrefix (poll pid budget) w (seed prior)).1,
        (runPrefix (poll pid budget) w (seed prior)).2.filterMap groEvent) := by
  have hp := poll_gro pid budget w (seed prior)
  rw [seed_gro] at hp
  cases hr : (runPrefix (poll pid budget) w (seed prior)).1 <;>
    simpa only [hr, Except.map, id] using hp

/-- Arbitrary valid previous lifetime history is retained in the same joint
execution; its reached access prefix is safe even if the poll Stops. -/
theorem poll_safe_suffix (pid : PeerId) (budget : Nat) (w : World)
    (prior : List LifetimeEvent) (hi : AllocationInv prior w) :
    ∃ suffix, (runPrefix (poll pid budget) w (seed prior)).2 = seed prior ++ suffix ∧
      LifetimeEvent.Safe (prior ++ suffix.filterMap accessEvent) ∧
      (match (runPrefix (poll pid budget) w (seed prior)).1 with
       | .error _ => True
       | .ok (_, v) => AllocationInv (prior ++ suffix.filterMap accessEvent) v) := by
  obtain ⟨suffix, hs⟩ := poll_appends pid budget w (seed prior)
  have hp := (poll_access pid budget).preserves
    (rxPollStackPrefix_preserves allocationAmbient allocationTx allocationRx allocationWgXmit pid budget)
    w (seed prior) (by simpa using hi)
  rw [hs, List.filterMap_append, seed_access] at hp
  refine ⟨suffix, hs, hp.1, ?_⟩
  cases hr : (runPrefix (poll pid budget) w (seed prior)).1 <;> simpa only [hr] using hp.2

/-- A normal original getter captures its resident allocation identity, which
cannot have been released in the incoming history. This is a reached getter
cut, not whole-poll distinctness. -/
theorem capture_fresh (skb : SkbId) (w v : World) (h : List Event)
    (pkt : RxPacket) (stamp : PacketStamp)
    (hi : AllocationInv (h.filterMap accessEvent) w)
    (hr : (runPrefix (capture skb) w h).1 = .ok ((pkt, stamp), v)) :
    v = w ∧ stamp = packetStamp w skb ∧
      ¬ AccessEvent.Released ((h.filterMap accessEvent).filterMap LifetimeEvent.packet?) stamp := by
  rw [capture_run] at hr
  cases hg : (getRxSkb skb).run w with
  | error e => simp [hg] at hr
  | ok out =>
    rcases out with ⟨p, u⟩
    simp only [hg, Except.ok.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    obtain ⟨rfl, d, hd, hp⟩ := Packets.getRxSkb_current skb w u p hg
    refine ⟨rfl, rfl, ?_⟩
    intro released
    exact hi.release.1.packet.2 _ released (.inr skb)
      (by simp [packetResidents, packetStamp, hd, hp])

/-- The actual free performs its original getter and emits the read/release
pair. Failure at that getter emits neither event. -/
theorem free_run (skb : SkbId) (w : World) (h : List Event) :
    runPrefix (access (freeRxSkbPrefix skb)) w h =
      match (getRxSkb skb).run w with
      | .error e => (.error e, h)
      | .ok (_, _) => ((freeRxSkb skb).run w,
          h ++ [.access (.packet (.read (.inr skb) (packetStamp w skb))),
                .access (.packet (.release (.inr skb) (packetStamp w skb)))]) := by
  unfold access
  cases hr : (getRxSkb skb).run w with
  | error e =>
    simpa only [List.map_nil, List.append_nil] using
      focusPrefix_suffix Event.access accessEvent (freeRxSkbPrefix skb) w h (.error e) []
        (by simp only [freeRxSkbPrefix_run, hr, List.append_nil])
  | ok out => exact focusPrefix_suffix _ _ _ _ _ _ _ (by rw [freeRxSkbPrefix_run, hr])

/-- Entry is recorded before the actual callback, and survives callback
failure. It is not a successful-delivery marker. -/
theorem enter_suffix (e : Entry) (w : World) (h : List Event) :
    ∃ suffix, (runPrefix (enter e) w h).2 = h ++ [.entered e] ++ suffix := by
  unfold enter
  rw [runPrefix_bind, runPrefix_emit]
  exact Appends.focus _ _ _ w (h ++ [.entered e])

/-- Original GRO selection and occurrence provenance transfer through the
same joint execution. These are local occurrence facts, not stamp uniqueness. -/
theorem poll_callback_tags (pid : PeerId) (budget : Nat) (w : World) (prior : List LifetimeEvent) :
    let h := (runPrefix (poll pid budget) w (seed prior)).2.filterMap groEvent
    ((enteredEntries h).map GroEntry.occurrence).Nodup ∧
      ∀ e ∈ enteredEntries h, e ∈ bufferedEntries h ∧ (e.occurrence, e.skb) ∈ removedTags h := by
  have he := congrArg Prod.snd (poll_fresh_gro pid budget w prior)
  dsimp only at he ⊢
  rw [← he]
  exact rxPollGro_callback_provenance pid budget w

end Leanux.Proofs.WG.Queues.RxJoint
