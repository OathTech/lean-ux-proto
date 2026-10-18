import Leanux.Proofs.WG.AuthenticatedEffects.TimerCarrier

/-! The native wheel selector returns an actual resident timer occurrence.
The carrier is explicit until transported through the complete driver. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots
open Leanux Leanux.WG

private def choose (acc : Option (PeerId × PeerTimer × WheelEntry))
    (candidate : PeerId × PeerTimer × WheelEntry) :=
  match acc with
  | none => some candidate
  | some prior => if TimerWheel.runsBefore candidate.2.2 prior.2.2 then some candidate else some prior

private theorem fold_selects (xs : List (PeerId × PeerTimer × WheelEntry))
    (initial : Option (PeerId × PeerTimer × WheelEntry)) (selected : PeerId × PeerTimer × WheelEntry)
    (result : xs.foldl choose initial = some selected) : selected ∈ xs ∨ initial = some selected := by
  induction xs generalizing initial with
  | nil => exact Or.inr result
  | cons x xs ih =>
    have tail := ih (choose initial x) result
    rcases tail with member | head
    · exact Or.inl (List.mem_cons_of_mem x member)
    · cases initial with
      | none =>
        have same : x = selected := Option.some.inj head
        exact Or.inl (by simp [same])
      | some old =>
        dsimp only [choose] at head
        split at head
        · have same : x = selected := Option.some.inj head
          exact Or.inl (by simp [same])
        · exact Or.inr head

theorem nextDue_member (d : Device) (j : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
    (selected : TimerWheel.nextDue d j = some (pid,timer,entry)) :
    (pid,timer,entry) ∈ TimerWheel.due d j := by
  rcases fold_selects (TimerWheel.due d j) none (pid,timer,entry) selected with member | impossible
  · exact member
  · cases impossible

theorem due_resident (d : Device) (j : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
    (member : (pid,timer,entry) ∈ TimerWheel.due d j) :
    ∃ p, d.peers[pid]? = some p ∧ p.wheel timer = some entry := by
  obtain ⟨source,_,found⟩ := List.mem_flatMap.mp member
  simp only [Std.TreeMap.get?_eq_getElem?] at found
  cases resident : d.peers[source]? with
  | none => simp [resident] at found
  | some p =>
    simp only [resident] at found
    obtain ⟨kind,_,picked⟩ := List.mem_filterMap.mp found
    cases wheel : p.wheel kind with
    | none => simp [wheel] at picked
    | some e =>
      simp only [wheel,Option.bind_some] at picked
      split at picked
      · have same := Option.some.inj picked
        cases same
        exact ⟨p,resident,wheel⟩
      · cases picked

/-- The exact native selector preserves timer kind, peer incarnation, expiry
and enqueue-stamped wheel entry when retrieving the stored cause. -/
theorem nextDue_cause (h : List TimerRoot.Event) (w : WGWorld) (d : Device)
    (device : w.dev = some d) (carrier : Carrier h w)
    (j : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
    (selected : TimerWheel.nextDue d j = some (pid,timer,entry)) :
    ∃ stamp expires, HasCause h pid timer stamp expires entry := by
  obtain ⟨p,resident,wheel⟩ := due_resident d j pid timer entry (nextDue_member d j pid timer entry selected)
  refine ⟨p.internalId,p.timer timer,carrier pid timer p.internalId (p.timer timer) entry ?_⟩
  simp [Pending,view,device,resident,wheel]

end Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots
