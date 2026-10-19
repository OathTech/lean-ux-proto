import Leanux.Proofs.WG.TransmitSecurity.StagedObligationQueues
import Leanux.Proofs.WG.TransmitSecurity.StagedExactFrames

/-! Exact projected-state and history frames for the fixed staged-ticket ledger.
The invariant ranges over missing queues too; deleting a queue is not a frame. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Staged.Origins AuthenticatedEffects.CausalJournal

theorem stagedPackets_views (epoch : Packets.epoch v = Packets.epoch w)
    (queues : stagedAt v = stagedAt w) (generation : Nat) (pid : PeerId) (stamp : Nat) :
    stagedPackets generation pid stamp v = stagedPackets generation pid stamp w := by
  simp only [stagedPackets,epoch,queues]

/-- An exact queue/epoch frame retains the obligations of every peer allocation,
including allocations whose native queue is absent. -/
theorem QueueInv.views (before : QueueInv history ledger w)
    (epoch : Packets.epoch v = Packets.epoch w) (queues : stagedAt v = stagedAt w) :
    QueueInv history ledger v := by
  intro generation pid stamp
  rw [stagedPackets_views epoch queues]
  exact before generation pid stamp

theorem QueueInv.append_history (before : QueueInv history ledger w) (suffix : List Event) :
    QueueInv (history ++ suffix) ledger w := by
  intro generation pid stamp
  exact (before generation pid stamp).history_append suffix

theorem QueueInv.views_append (before : QueueInv history ledger w) (suffix : List Event)
    (epoch : Packets.epoch v = Packets.epoch w) (queues : stagedAt v = stagedAt w) :
    QueueInv (history ++ suffix) ledger v :=
  (before.views epoch queues).append_history suffix

/-- A missing or empty projected native queue cannot hide a pending ledger
obligation: its exact filtered list of staged tickets must be empty. -/
theorem QueueInv.empty_pending (before : QueueInv history ledger w)
    (empty : stagedPackets generation pid stamp w = []) :
    pendingAt (.staged generation pid stamp) ledger = [] := by
  have alignment := before generation pid stamp
  rw [empty] at alignment
  have nil_right (tickets : List Ticket)
      (related : Aligned (Born history generation pid stamp) tickets []) : tickets = [] := by
    cases related
    rfl
  exact nil_right _ alignment

theorem QueueInv.absent_pending (before : QueueInv history ledger w)
    (absent : stagedAt w pid = none) (generation stamp : Nat) :
    pendingAt (.staged generation pid stamp) ledger = [] := by
  apply before.empty_pending
  simp [stagedPackets,absent]

theorem QueueInv.other_epoch_pending (before : QueueInv history ledger w)
    (different : Packets.epoch w ≠ some generation) (pid : PeerId) (stamp : Nat) :
    pendingAt (.staged generation pid stamp) ledger = [] := by
  apply before.empty_pending
  simp [stagedPackets,different]

theorem queue_initial (net bare : Bool) : QueueInv [] [] (Runner.initialWG net bare) := by
  intro generation pid stamp
  have absent : stagedAt (Runner.initialWG net bare) pid = none := by
    cases net <;> cases bare <;> simp [stagedAt,Runner.initialWG]
  have empty : stagedPackets generation pid stamp (Runner.initialWG net bare) = [] := by
    simp [stagedPackets,absent]
  rw [empty]
  exact .nil

/-- A completed native action transports the unchanged ledger only when it
preserves both projected views exactly. No deletion-retaining frame is used. -/
theorem queue_frame {action : WG.M α} (epoch : SameView Packets.epoch action)
    (queues : SameView stagedAt action) : Preserves (QueueInv history ledger) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  exact before.views
    ((ProjectedAction.iff_run_ambient _ _ _).mp epoch w a value v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp queues w a value v b run)

/-- An observed exact native frame may append history while keeping the same
fixed ledger. Failed executions retain their actual append history; this does
not claim a post-state for Stop. -/
theorem queue_observed_frame {action : WGPrefix Event α} {native : WG.M α}
    (appends : StateAppends action) (erases : ErasesStatePrefix action native)
    (epoch : SameView Packets.epoch native) (queues : SameView stagedAt native) :
    StatePrefixPreserves (fun h w _ => QueueInv h ledger w) (fun _ => True) action := by
  intro w a h before
  obtain ⟨suffix,position⟩ := appends w a h
  refine ⟨suffix,position,True.intro,?_⟩
  cases outcome : (runPrefix (action.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have run : (native.run w).run a = .ok ((value,v),b) := (erases w a h).symm.trans outcome
    have kept := (hoare_iff_run_ambient _ _ _).mp (queue_frame epoch queues)
      w a value v b before run
    rw [position]
    exact kept.append_history suffix

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
