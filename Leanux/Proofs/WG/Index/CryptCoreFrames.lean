import Leanux.Proofs.WG.Index.ConfigurationIndexFrames
import Leanux.Proofs.WG.Index.TimerCoreSource
import Leanux.Proofs.WG.Index.StagingIndexEffects
import Leanux.Proofs.WG.Index.OwnerCoherenceKeypairReleaseClaims
import Leanux.Proofs.WG.Queues.HolderAuxScheduler
import Leanux.Proofs.WG.Queues.BaseCoherenceWorkers
import Leanux.Proofs.WG.Noise.PendingCryptSource
import Leanux.Proofs.WG.Index.LookupCoreSource
import Leanux.Proofs.WG.Queues.BaseCoherenceHistory
import Leanux.Proofs.WG.Index.ConfigurationCreationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.CryptCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem skb {α : Type} (action : SkbM α) :
    Preserves Reached.Core (liftSkb action) := by
  apply ConfigurationIndex.frame_core
  intro initial
  apply hoare_liftSkb
  intro w d store pre device
  simpa only [ConfigurationIndex.fields,ConfigurationIndex.deviceFields,senderDeviceCell,
    device,Option.map_some] using pre

theorem saved_peer (pid : PeerId) (p q : Peer)
    (same : senderPeerCell q=senderPeerCell p) :
    Hoare (setPeer pid q) (fun w => Reached.Core w ∧ peerAt w pid=some p)
      (fun _ => Reached.Core) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  cases device : w.dev with
  | none => simp [peerAt,device] at pre
  | some d =>
    have resident : d.peers[pid]?=some p := by simpa [peerAt,device] using pre.2
    cases run
    apply ConfigurationIndex.fields_core _ _ ?_ pre.1
    simpa [ConfigurationIndex.fields,device] using congrArg some
      (ConfigurationIndex.deviceFields_peerWrite d pid p q resident same)

theorem skb_peer {α : Type} (action : SkbM α) (pid : PeerId) (p : Peer) :
    Preserves (fun w => Reached.Core w ∧ peerAt w pid=some p) (liftSkb action) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  have frame : SameView (fun w => peerAt w pid) (liftSkb action) := by
    intro initial
    apply hoare_liftSkb
    intro w d store pre device
    simpa only [peerAt,device,Option.bind_some] using pre
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (skb action) w a result v b pre.1 run,
    ((ProjectedAction.iff_run_ambient _ _ _).mp frame w a result v b run).trans pre.2⟩

end Leanux.Proofs.WG.Index.CryptCore
