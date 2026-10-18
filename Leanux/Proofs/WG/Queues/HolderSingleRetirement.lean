import Leanux.Proofs.WG.Queues.HolderBaseRetirement

/-! One-peer removal pays its unique live base occurrence. This local
contract states the list coherence it needs; it does not assume it initialized. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem unique_detached (base : Reservations) (pid : PeerId)
    (unique : (base.map Owner.slot).Nodup) (present : pid ∈ base.map Owner.slot) :
    ∃ o, o.slot = pid ∧ BaseRemoval.detached base pid = [o] := by
  induction base with
  | nil => simp at present
  | cons o rest ih =>
    simp only [List.map_cons,List.nodup_cons] at unique
    by_cases same : o.slot = pid
    · have empty : BaseRemoval.detached rest pid = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x member equal
        have slot : x.slot = pid := by simpa only [beq_iff_eq] using equal
        exact unique.1 (by rw [same]; exact List.mem_map.mpr ⟨x,member,slot⟩)
      refine ⟨o,same,?_⟩
      simp only [BaseRemoval.detached,List.filter_cons,same,beq_self_eq_true,ite_true]
      exact congrArg (o :: ·) empty
    · have inside : pid ∈ rest.map Owner.slot := by simpa [same,Ne.symm same] using present
      obtain ⟨x,slot,detached⟩ := ih unique.2 inside
      exact ⟨x,slot,by simpa [BaseRemoval.detached,same] using detached⟩

/-- The single removal selects its one supplied live base occurrence, then
keeps it charged through both real drains until the final source payment. -/
theorem peerRemove_some_funded (pid : PeerId) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (unique : (holders.base.map Owner.slot).Nodup)
    (present : pid ∈ holders.base.map Owner.slot) (a b : Ambient)
    (run : ((peerRemove (some pid)).run w).run a = .ok (((),v),b)) :
    DuringWork (holders.withoutBase (BaseRemoval.live holders.base pid)) cs loans v := by
  obtain ⟨o,slot,one⟩ := unique_detached holders.base pid unique present
  change ((peerMakeDead pid >>= fun _ => peerRemoveAfterDead pid).run w).run
    (CounterWindow.record a .peerRemoveNull false) = .ok (((),v),b) at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,marked,c,mark,pay⟩ := run
  cases u
  obtain ⟨funded,stable⟩ := peerMakeDead_funded pid hi stable _ c mark
  rw [one,List.singleton_append] at funded
  exact afterDead_normal (duringWork_initial funded stable) c b (by simpa only [slot] using pay)

theorem peerRemove_none_funded {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((peerRemove none).run w).run a = .ok (((),v),b)) :
    holders.Funded cs loans v ∧ StableRx cs v := by
  change Except.ok (((),w),CounterWindow.record a .peerRemoveNull true) = .ok (((),v),b) at run
  cases run
  exact ⟨hi,stable⟩

theorem peerRemove_some_observed (pid : PeerId) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (unique : (holders.base.map Owner.slot).Nodup)
    (present : pid ∈ holders.base.map Owner.slot) (a b : Ambient)
    (history : List LifetimeEvent)
    (run : (runStatePrefix (peerRemovePrefix (some pid)) w a history).1 = .ok (((),v),b)) :
    DuringWork (holders.withoutBase (BaseRemoval.live holders.base pid)) cs loans v :=
  peerRemove_some_funded pid hi stable unique present a b
    ((peerRemovePrefix_erases (some pid) w a history).symm.trans run)

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
