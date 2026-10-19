import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityActualSelection
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietEffects

/-! Exact native erasure of actual terminal-labelled TX creation. The
separate quiet-source facts account for every retained observation. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

theorem create_actual_erases (pid : PeerId) (items : List SkbId) :
    ErasesStatePrefix (CausalJournal.create pid items) (createData pid items) := by
  have oldErase : ErasesStatePrefix (Journal.create pid items) (createData pid items) :=
    NativeAdapter.lower_erases
      (focusPrefix_erases _ _ (TxDisposition.create_erases pid items))
  intro w a h
  have projected := congrArg Prod.fst (CausalJournal.create_projects pid items w a h)
  have maps : (fun x : (Unit × WGWorld) × Ambient => (Prod.map id id x.1,x.2)) = id := by
    funext ⟨⟨value,v⟩,b⟩
    rfl
  change (runWGPrefix (Journal.create pid items) w a (h.filterMap old?)).1 =
    (runWGPrefix (CausalJournal.create pid items) w a h).1.map
      (fun x => (Prod.map id id x.1,x.2)) at projected
  rw [maps,Except.map_id] at projected
  exact projected.symm.trans (oldErase w a (h.filterMap old?))

theorem queued_actual_erases (pid : PeerId) (retry : Bool) :
    ErasesStatePrefix (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid retry)
      (sendQueuedHandshakeInitiation pid retry) := by
  intro w a h
  have projected := congrArg Prod.fst
    (CallbackQuiet.queued_projects allocation? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid retry w a h)
  have maps : (fun x : (Unit × WGWorld) × Ambient => (Prod.map id id x.1,x.2)) = id := by
    funext ⟨⟨value,v⟩,b⟩
    rfl
  change ((sendQueuedHandshakeInitiation pid retry).run w).run a =
    (runWGPrefix (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid retry) w a h).1.map
      (fun x => (Prod.map id id x.1,x.2)) at projected
  rw [maps,Except.map_id] at projected
  exact projected.symm

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
