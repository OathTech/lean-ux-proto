import Leanux.Proofs.WG.TimerDiscipline.HookStateAtomsSource
import Leanux.Proofs.WG.TimerDiscipline.HookStateNativeSource
/-! Concrete quiet-leaf assembly for invariants transported by nondecreasing allocation counters. Hook-bearing transmit/receive/NAPI/send observers remain explicit in the generic scheduler and deferred source rules. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookState
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Std.Do
open Keypairs Keypairs.WGFrames Keypairs.WGTransitions Keypairs.EnvFrames
variable {E : Type} {I : List E → World → Prop} {S : List E → Prop}
theorem scheduler_leaves (safe : ∀ h w, I h w → S h) (transport : CounterTransport I) :
    HookScheduler.StateLeaves I S := by
  constructor
  · apply scheduler_atoms safe (counter_store transport)
    intro f
    apply ordinary_lift safe transport
    apply OrdinaryAction.liftWG
    apply Keypairs.SameView.ordinary
    exact fun initial => modifyDev_snapshot_spec (fun s=>s=initial) _ (fun _=>rfl)
  · exact ordinary_lift safe transport _ (OrdinaryAction.liftWG (Keypairs.SameView.ordinary poll_snapshot))
  · intro item
    exact ordinary_lift safe transport _ (encryptTail_ordinary item)
  · exact ordinary_lift safe transport _ (OrdinaryAction.liftWG (Keypairs.SameView.ordinary prepare_snapshot))
  · intro pid
    exact ordinary_lift safe transport _ (OrdinaryAction.liftWG (Keypairs.SameView.ordinary (peerPut_sameSnapshot (some pid))))
theorem deferred_leaves (safe : ∀ h w, I h w → S h) (transport : CounterTransport I) :
    HookDeferred.StateLeaves I S :=
  ⟨deferred_atoms safe (counter_store transport),
    ordinary_lift safe transport _ runOneClearWorker_ordinary,
    fun worker pid timer wheel prior => ordinary_lift safe transport _ (timer_ordinary worker pid timer wheel prior),
    fun j => ordinary_lift safe transport _ (placeholder_ordinary j)⟩
end Leanux.Proofs.WG.TimerDiscipline.HookState
