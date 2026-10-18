import Leanux.Proofs.WG.Noise.DriverTagProductSource
import Leanux.Proofs.WG.Noise.DriverTagFlushCallerSource
import Leanux.Proofs.WG.Queues.SendEnvironment
import Leanux.Proofs.WG.Queues.EnvClearDispatch
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Dispatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def oneObserved (queue : Device → List PeerId) (worker : Worker) (missing : String)
    (body : PeerId → ProductObs Unit) : ProductObs Unit := do
  let d ← liftPrefix (liftWG getDev)
  let some headPid := (queue d).head? | liftPrefix (invariant missing)
  let pid ← match ← liftPrefix (peekUnit worker) with
    | some u => liftPrefix (resolveUnit worker u (queue d))
    | none => pure headPid
  body pid

theorem one_erases (queue : Device → List PeerId) (worker : Worker) (missing : String)
    (body : PeerId → ProductObs Unit) (native : PeerId → Leanux.M Unit)
    (erases : ∀ pid, ErasesPrefix (body pid) (native pid)) :
    ErasesPrefix (oneObserved queue worker missing body) (do
      let d ← liftWG getDev
      let some headPid := (queue d).head? | invariant missing
      let pid ← match ← peekUnit worker with
        | some u => resolveUnit worker u (queue d)
        | none => pure headPid
      native pid) := by
  unfold oneObserved
  repeat' first
    | exact erases _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

theorem one_preserves (entry : TagMap) (queue : Device → List PeerId)
    (worker : Worker) (missing : String) (body : PeerId → ProductObs Unit)
    (hb : ∀ pid, PrefixPreserves (StateInv entry) ValidHistory (body pid)) :
    PrefixPreserves (StateInv entry) ValidHistory (oneObserved queue worker missing body) := by
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves (StateInv entry) ValidHistory
        (liftPrefix (liftAmbient a)) :=
    lift_product_store entry _ (fun _ => productAmbient_spec a _ (fun _ _ hi => hi))
  unfold oneObserved
  apply PrefixPreserves.bind (lift_product_store entry _ (liftWG_sameProductStore getDev getDev_sameWGStore))
  intro d
  split
  · apply PrefixPreserves.bind (ambient (AmbientM.peekUnit worker))
    intro unit
    cases unit with
    | none => exact (PrefixPreserves.pure (safe entry) _).bind hb
    | some u => exact (ambient (AmbientM.resolveUnit worker u (queue d))).bind hb
  · exact ambient (AmbientM.invariant missing)

def runOneSendObserved : ProductObs Unit :=
  oneObserved (·.sendWorkQueue) .sendWorker "no queued handshake send work"
    (fun pid => liftWGObserver (Flush.runFlushedSendObserved pid))

def runOneClearObserved : ProductObs Unit :=
  oneObserved (·.clearWorkQueue) .clearPeerWorker "no queued clear work"
    (fun pid => liftWGObserver (Flush.runFlushedClearObserved pid))

theorem runOneSendObserved_erases : ErasesPrefix runOneSendObserved Env.runOneSendWorker := by
  rw [RxCredits.SendEnvironment.runOneSendWorker_factor]
  exact one_erases _ _ _ _ _ (fun pid => liftWGObserver_erases (Flush.runFlushedSendObserved_erases pid))

theorem runOneClearObserved_erases : ErasesPrefix runOneClearObserved Env.runOneClearWorker := by
  rw [RxCredits.ClearWork.runOneClearWorker_factor]
  exact one_erases _ _ _ _ _ (fun pid => liftWGObserver_erases (Flush.runFlushedClearObserved_erases pid))

theorem runOneSendObserved_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory runOneSendObserved :=
  one_preserves entry _ _ _ _ (fun pid => (Flush.runFlushedSendObserved_preserves entry pid).liftWGObserver)

theorem runOneClearObserved_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory runOneClearObserved :=
  one_preserves entry _ _ _ _ (fun pid => (Flush.runFlushedClearObserved_preserves entry pid).liftWGObserver)

end Leanux.Proofs.WG.Noise.DriverTags.Dispatch

