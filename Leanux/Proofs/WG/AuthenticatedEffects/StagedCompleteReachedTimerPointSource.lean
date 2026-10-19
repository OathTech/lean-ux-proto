import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointConsume
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductNapi

/-! Fixed timer callback syntax. Work subtrees are their canonical source
witnesses. Purge and zero-key interiors are refined separately below. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
abbrev History := List Event
abbrev Result (α : Type) := Except Stop (α × World)
abbrev Carrier := WorkService.Points.Carrier
abbrev Checked (action : PrefixM Event α) := WorkService.Points.Checked action
abbrev Failure (action : PrefixM Event α) := WorkService.Points.Failure action
abbrev wg (body : WG.M α) := Consume.Leaf.wg body

inductive Native where
  | world
  | history
  | selected (receipt : TimerDispatch.Selection)
  | scope (event : CausalScope.Event Cause)

def Native.Result : Native → Type
  | .world => World
  | .history => History
  | _ => Unit

def Native.action (token : Native) : PrefixM Event token.Result := match token with
  | .world => liftPrefix get
  | .history => Consume.Leaf.historyRead
  | .selected receipt => emitPrefix (.old (.timerSelected receipt))
  | .scope event => emitPrefix (.scope event)

inductive Child where
  | release (peer : Option PeerId)
  | flushedSend (pid : PeerId)
  | keepalive (pid : PeerId)
  | purge (pid : PeerId)
  | zero (pid : PeerId)

def Child.action : Child → PrefixM Event Unit
  | .release peer => liftWGObserver (peerRelease peer)
  | .flushedSend pid => liftWGObserver (CausalJournal.flushedSend pid)
  | .keepalive pid => liftWGObserver (Driver.keepaliveObserved hooks pid)
  | .purge pid => liftWGObserver (stagedPurge pid)
  | .zero pid => wg (expiredZeroKeyMaterial pid)

def workChild : WorkService.Points.Child → Child
  | .release peer => .release peer
  | .flushedSend pid => .flushedSend pid

inductive Label where
  | callback (pid : PeerId) (timer : PeerTimer)
  | selected (device : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
  | finished (token : Nat)

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (token : Native) : Shape token.action
  | work (source : WorkService.Points.Shape action) : Shape action
  | child (token : Child) : Shape token.action
  | failed {α β : Type} {body : PrefixM Event α} (failure : Failure body) (next : α → PrefixM Event β) : Shape (body >>= next)
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value)) : Shape (body >>= next)
  | marked (label : Label) (shape : Shape action) : Shape action
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points
