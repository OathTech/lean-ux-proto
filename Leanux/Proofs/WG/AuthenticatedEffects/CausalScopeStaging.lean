import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeEffects

/-! Staging and keepalive restore their incoming lexical stack. They may emit
native effects under that stack; root authorization is a separate invariant. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem old_state (body : WGPrefix Journal.Event α) : StateSafe (state body) :=
  state_focus Event.old old? (fun _ => rfl) body

theorem old_product (body : PrefixM Journal.Event α) : ProductSafe (product body) :=
  product_focus Event.old old? (fun _ => rfl) body

theorem session (pid : PeerId) : StateSafe (CausalJournal.session pid) :=
  state_receipt _ (old_state _) _ (fun _ => rfl)

theorem no_key (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    StateSafe (PacketEffects.noKeyWith effects pid packets keypair invalid) := by
  unfold PacketEffects.noKeyWith
  repeat' first
    | (scope_balance_head TimerEffects.queuedWith; exact queued _ _)
    | scope_effect_step

theorem staging (pid : PeerId) : StateSafe (Driver.stagingObserved hooks pid) := by
  unfold Driver.stagingObserved
  repeat' first
    | (scope_balance_head PacketEffects.noKeyWith; exact no_key _ _ _ _)
    | (scope_balance_head Driver.Hooks.selection; exact old_state _)
    | (scope_balance_head Driver.Hooks.reserve; exact old_state _)
    | (scope_balance_head Driver.Hooks.allocate; exact old_state _)
    | (scope_balance_head Driver.Hooks.create; exact old_state _)
    | scope_state_step

theorem keepalive (pid : PeerId) : StateSafe (Driver.keepaliveObserved hooks pid) := by
  unfold Driver.keepaliveObserved
  repeat' first
    | (scope_balance_head Driver.Hooks.keepalivePrepare; exact state_receipt _ (state_lift _) _ (fun _ => rfl))
    | (scope_balance_head Driver.stagingObserved; exact staging _)
    | scope_state_step

theorem transmit_front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (Driver.transmitObserved hooks family addr packets mtu) := by
  unfold Driver.transmitObserved
  repeat' first
    | (scope_balance_head Driver.Hooks.front; exact old_state _)
    | (scope_balance_head Driver.stagingObserved; exact staging _)
    | scope_state_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
