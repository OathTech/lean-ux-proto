import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableNative
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityStaging

/-! The disposal journal retains the existing live-birth carrier. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects.CausalJournal

theorem peer_release_observed (peer : Option PeerId) : StateSafe (AuthenticatedEffects.CausalJournal.peerRelease peer) :=
  state_quiet (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other Event.stagedDisposal stagedDisposal? allocation? (fun _ => rfl)
      ((HandshakeSecurity.StagedDisposal.releaseObserved peer).run w))
    (focusStatePrefix_erases _ _ (HandshakeSecurity.StagedDisposal.release_erases peer))
    (fun _ => Native.peer_put peer)

theorem staged_purge_observed (pid : PeerId) : StateSafe (AuthenticatedEffects.CausalJournal.stagedPurge pid) :=
  state_quiet (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other Event.stagedDisposal stagedDisposal? allocation? (fun _ => rfl)
      ((HandshakeSecurity.StagedDisposal.purgeObserved pid).run w))
    (focusStatePrefix_erases _ _ (HandshakeSecurity.StagedDisposal.purge_erases pid))
    (fun _ => Native.purge pid)

theorem disposal_history (body : WGPrefix HandshakeSecurity.StagedDisposal.Event α) :
    Driver.StateHistorySafe Safe (focusStatePrefix Event.stagedDisposal stagedDisposal? body) := by
  intro w a h hi
  let suffix := ((runWGPrefix body w a (h.filterMap stagedDisposal?)).2.drop
    (h.filterMap stagedDisposal?).length).map Event.stagedDisposal
  have good : Safe (h ++ suffix) := hi.quiet (by
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    rfl)
  refine ⟨suffix,rfl,good,?_⟩
  cases (runPrefix (StateT.run (focusStatePrefix Event.stagedDisposal stagedDisposal? body) w) a h).1 <;> trivial

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
