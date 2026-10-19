import Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntryWorkers

/-! Exact draining scheduler composition for replay-entry certificates.
Copied consistency trials retain their original native semantics. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Keypairs TransmitSecurity.Driver
open Keypairs.Observers Keypairs.WGConfig
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

theorem product_throw (err : Stop) : ProductSafe (liftPrefix (throw err : Leanux.M α)) := by
  intro w h hi
  exact ⟨[],by simp,hi.2,True.intro⟩

open Lean Meta Elab Tactic in
elab "replay_product_native " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductSafe do throwError "not a product carrier contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``liftPrefix do throwError "not a native product lift"
  let native := action.getAppArgs.back!.consumeMData.headBeta
  let .const actual _ := native.getAppFn | throwError "not a native constant"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different native head"

macro "replay_scheduler_native" : tactic => `(tactic| first
  | (replay_product_native liftWG
     apply product_wg
     repeat' first | observer_ordinary_leaf | ordinary_strict_step)
  | (first | replay_product_native getAmbient | replay_product_native modifyAmbient
           | replay_product_native peekHiddenSite | replay_product_native invariant
     exact product_ambient _)
  | (replay_product_native throw; exact product_throw _))

theorem crypt_ahead (pid : PeerId) : ProductSafe (cryptAheadObserved hooks pid) := by
  unfold cryptAheadObserved
  repeat' first
    | (replay_entry_head encryptIterObserved; exact encrypt_iteration)
    | solve | replay_scheduler_native
    | replay_entry_product_step
  all_goals exact product_throw _

theorem iteration (act : Activation) : ProductSafe (iterationObserved hooks act) := by
  unfold iterationObserved
  repeat' first
    | (replay_entry_head encryptIterObserved; exact encrypt_iteration)
    | (replay_entry_head decryptIterObserved; exact decrypt_iteration)
    | (replay_entry_head receiveIterObserved; exact receive_iteration)
    | (replay_entry_head txIterObserved; exact tx_iteration _)
    | (replay_entry_head cryptAheadObserved; exact crypt_ahead _)
    | solve | replay_scheduler_native
    | replay_entry_product_step

theorem schedule (stack : Option Worker) : ProductSafe (scheduleObserved hooks stack) := by
  apply SourceScheduler.schedule_preserves (fun _ _ hi => hi.2) product_store
  · intro pid
    apply product_wg
    repeat' first | observer_ordinary_leaf | ordinary_strict_step
  · exact iteration
  · exact softirq

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
