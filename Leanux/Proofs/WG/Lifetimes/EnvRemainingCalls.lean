import Leanux.Proofs.WG.Lifetimes.EnvBatchAudit

/-! Fifteen original environment controls, observation, ingress and batch calls.
Local AuditInv preservation includes actual reached scheduler probes, while the
enclosing syscall and initialized Runner contracts remain separate. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

inductive EnvRemainingCall where
  | up
  | mtu (value : Nat)
  | route
  | down
  | delete
  | deladdr (family : Nat)
  | delroute (family : Nat)
  | observe
  | inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat)
  | flood (count port family : Nat) (messages : List (List UInt8))
  | inlinePoll
  | afterBatch
  | batch (items : List Env.BatchItem)
  | cleanup
  | multicast (family addr : Nat)

namespace EnvRemainingCall

def Result : EnvRemainingCall → Type
  | .up => Int
  | .mtu _ => Int
  | .route => Unit
  | .down => Int
  | .delete => Int
  | .deladdr _ => Int
  | .delroute _ => Int
  | .observe => Int × Lean.Json
  | .inject _ _ _ _ _ _ => Int
  | .flood _ _ _ _ => Int
  | .inlinePoll => Unit
  | .afterBatch => Unit
  | .batch _ => Int
  | .cleanup => Unit
  | .multicast _ _ => Unit

def original : (call : EnvRemainingCall) → M call.Result
  | .up => Env.wgUp
  | .mtu value => Env.setMtu value
  | .route => Env.routeIntoWg0
  | .down => Env.wgDown
  | .delete => Env.wgDelete
  | .deladdr family => Env.wgDeladdr family
  | .delroute family => Env.wgDelroute family
  | .observe => Env.observe
  | .inject family port msg tos ll dest => Env.inject family port msg tos ll dest
  | .flood count port family messages => Env.flood count port family messages
  | .inlinePoll => Env.pollScheduledInline
  | .afterBatch => Env.afterBatch
  | .batch items => Env.batch items
  | .cleanup => Env.netnsCleanup
  | .multicast family addr => Env.xmitMulticastLoop family addr

def observed : (call : EnvRemainingCall) → AuditM call.Result
  | .up => envWgUpAudit
  | .mtu value => setMtuAudit value
  | .route => routeIntoWg0Audit
  | .down => envWgDownAudit
  | .delete => envWgDeleteAudit
  | .deladdr family => wgDeladdrAudit family
  | .delroute family => wgDelrouteAudit family
  | .observe => observeAudit
  | .inject family port msg tos ll dest => injectAudit family port msg tos ll dest
  | .flood count port family messages => floodAudit count port family messages
  | .inlinePoll => pollScheduledInlineAudit
  | .afterBatch => afterBatchAudit
  | .batch items => batchAudit items
  | .cleanup => envNetnsCleanupAudit
  | .multicast family addr => xmitMulticastLoopAudit family addr

theorem erases (call : EnvRemainingCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | up => exact envWgUpAudit_erases
  | mtu value => exact setMtuAudit_erases value
  | route => exact routeIntoWg0Audit_erases
  | down => exact envWgDownAudit_erases
  | delete => exact envWgDeleteAudit_erases
  | deladdr family => exact wgDeladdrAudit_erases family
  | delroute family => exact wgDelrouteAudit_erases family
  | observe => exact observeAudit_erases
  | inject family port msg tos ll dest => exact injectAudit_erases family port msg tos ll dest
  | flood count port family messages => exact floodAudit_erases count port family messages
  | inlinePoll => exact pollScheduledInlineAudit_erases
  | afterBatch => exact afterBatchAudit_erases
  | batch items => exact batchAudit_erases items
  | cleanup => exact envNetnsCleanupAudit_erases
  | multicast family addr => exact xmitMulticastLoopAudit_erases family addr

theorem preserves (call : EnvRemainingCall) : PrefixPreserves AuditInv AuditSafe call.observed := by
  cases call with
  | up => exact envWgUpAudit_preserves
  | mtu value => exact setMtuAudit_preserves value
  | route => exact routeIntoWg0Audit_preserves
  | down => exact envWgDownAudit_preserves
  | delete => exact envWgDeleteAudit_preserves
  | deladdr family => exact wgDeladdrAudit_preserves family
  | delroute family => exact wgDelrouteAudit_preserves family
  | observe => exact observeAudit_preserves
  | inject family port msg tos ll dest => exact injectAudit_preserves family port msg tos ll dest
  | flood count port family messages => exact floodAudit_preserves count port family messages
  | inlinePoll => exact pollScheduledInlineAudit_preserves
  | afterBatch => exact afterBatchAudit_preserves
  | batch items => exact batchAudit_preserves items
  | cleanup => exact envNetnsCleanupAudit_preserves
  | multicast family addr => exact xmitMulticastLoopAudit_preserves family addr

/-- Local allocation validity and empty history supply initial probe validity.
This does not supply the initialized outer Runner entry or its missing callers. -/
theorem from_allocation (call : EnvRemainingCall) (w : World) (hi : AllocationInv [] w) :
    AuditSafe (runPrefix call.observed w []).2 ∧
    ∀ p ∈ probeEntries (runPrefix call.observed w []).2,
      AllocationInv p.history p.world ∧
      (p.world.suspended.filterM Env.Activation.consistent).run p.world =
        (p.world.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.suspended, LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 := by
  have hs := (call.preserves w [] (audit_initial hi)).choose_spec.2.1
  exact ⟨hs, fun p hp => savedProbe_trials hs.2 hp⟩


end EnvRemainingCall
end Leanux.Proofs.WG.Lifetimes
