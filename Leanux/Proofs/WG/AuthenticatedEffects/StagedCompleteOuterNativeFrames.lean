import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTrafficFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryControlFrames

/-! Native outer frames preserve paired accounting without new history.
Only literal native lifts are extracted; observed callbacks with receipts are
never erased to manufacture a historical frame. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

theorem native_of_checked {action : Leanux.M α} (checked : Checked (liftPrefix action))
    (h : List Event) : Preserves (Carrier h) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w value v before run
  obtain ⟨suffix,extended,safe,post⟩ := checked w h before
  simpa only [runPrefix_lift,run] using post

theorem pre_exit : StateChecked (liftWGPrefix netnsPreExit) :=
  pair (CompletePassive.native Safe account_safe _ ControlFrames.pre_exit)
    (erasesStatePrefix_lift _)
    (AllocatedFrames.observed (DeviceControlCall.erases .preExit) (DeviceControlCall.allocation .preExit))

theorem cleanup_native (h : List Event) : Preserves (Carrier h) Env.netnsCleanup := by
  have preExit : Preserves (Carrier h) (monadLift netnsPreExit : Leanux.M Unit) :=
    native_of_checked (wg _ pre_exit) h
  have effects {α : Type} (a : AmbientM α) := native_of_checked (ambient a) h
  have routes {α : Type} (a : Net.M α) := native_of_checked (routing a) h
  have env (f : EnvWorld → EnvWorld) := native_of_checked (env_edit f) h
  routing_tx_source [Env.netnsCleanup,Env.runWorker,Env.pendingDevice,getAmbient,getRouting,peekUnit,resolveUnit,skipCut,unsupported,modifyAmbient,hidden]
    using [preExit,effects,routes,env]

theorem cleanup : Checked (liftPrefix Env.netnsCleanup) := native _ cleanup_native

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
