import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryHandshakeWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySavedFrames

/-! The send-worker prefix retains the saved peer's allocation and ordered
queues across its pending-flag update. This is an actual native prefix frame,
independent of the worker's later counted repayment. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.SendWorkerFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem create (pid : PeerId) : SameView StagedEntry.view (createInitiation pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch]
  repeat' entry_handshake_native_step initial

def beforeWorker (pid : PeerId) : WG.M Unit := do
  let p ← getPeer pid
  if !p.handshakePending then invariant "queued work without a pending flag"
  let d ← getDev
  setPeer pid {p with handshakePending := d.sendWorkQueue.contains pid}
  _ ← hidden (.sectionStart .sendWorker)

theorem before_frame (pid : PeerId) : SameView StagedEntry.view (beforeWorker pid) := by
  intro initial
  unfold beforeWorker
  apply hoare_bind _ _ (SavedFrames.read pid (· = initial))
  intro p
  let P := fun w => StagedEntry.view w = initial ∧ SavedFrames.PeerFields pid p w
  apply hoare_consequence (P := P) (Q := fun _ => P) ?_
    (fun _ before => before) (fun _ _ before => before.1)
  change Preserves P _
  simp only [getDev,hidden,invariant]
  repeat' first
    | (rx_retention_head setPeer; apply SavedFrames.write_saved pid p _ (· = initial); exact ⟨rfl,rfl,rfl⟩)
    | (rx_retention_head get; exact hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem after_factor (worker : PeerId → WGPrefix Event Unit) (pid : PeerId) :
    HandshakeSecurity.SendExchange.afterTakeWith liftWGPrefix worker pid =
      (do liftWGPrefix (beforeWorker pid)
          worker pid
          _ ← liftWGPrefix (hidden (.sectionStop .sendWorker))) := by
  unfold HandshakeSecurity.SendExchange.afterTakeWith beforeWorker
  simp only [Queued.lift_bind,bind_assoc]
  congr 1
  funext p
  split <;> simp only [Queued.lift_bind,bind_assoc,Queued.lift_pure,pure_bind]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.SendWorkerFrames
