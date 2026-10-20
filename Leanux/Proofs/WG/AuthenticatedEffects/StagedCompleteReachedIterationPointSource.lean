import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerPointCoverage
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionEntryAheadSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationReadSource

/-! Fixed original iteration source shapes. Committed worker children remain
finite explicit contracts; native copied-record guards are separate atoms.
No arbitrary equal-action witness constructs an iteration point. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Iteration.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

abbrev History := List Event
abbrev Result (α : Type) := Except Stop (α × World)

inductive Native : {α : Type} → Leanux.M α → Type 1 where
  | ambientAction (body : AmbientM α) : Native (Leanux.liftAmbient body)
  | ambient : Native getAmbient
  | peer (pid : PeerId) : Native (liftWG (getPeer pid))
  | packet (skb : SkbId) : Native (liftWG (getTxSkb skb))
  | hiddenSite : Native peekHiddenSite
  | appendWork (pid : PeerId) :
      Native (liftWG (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}))
  | eraseWork (pid : PeerId) :
      Native (liftWG (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid}))
  | advance (enc : Activation) : Native (modifyAmbient fun s =>
      {s with suspended := s.suspended.map fun x =>
        if x == enc then {x with iterations := x.iterations + 1} else x})
  | resched (worker : Worker) : Native (Env.condResched worker)
  | branch (site : Decision) (yes : Bool) : Native (Leanux.branch site yes)
  | invariant (message : String) : Native (Leanux.invariant message : Leanux.M α)
  | stopped (reason : Stop) : Native (throw reason : Leanux.M α)

inductive Child where
  | poll
  | softirq
  | irqExit
  | encrypt (item : Option (List SkbId))
  | transmit (pid : PeerId)
  | prepare
  | release (pid : PeerId)
  | handshake

def Child.Result : Child → Type
  | .poll => Option (List SkbId)
  | .softirq | .irqExit | .release _ => Unit
  | .prepare => Option PeerId
  | .encrypt _ | .transmit _ | .handshake => Bool

def Child.action (token : Child) : PrefixM Event token.Result :=
  match token with
  | .poll => hooks.poll
  | .softirq => Driver.softirqObserved hooks
  | .irqExit => Driver.irqExitObserved hooks
  | .encrypt item => hooks.encrypt item
  | .transmit pid => hooks.transmit pid
  | .prepare => hooks.prepare
  | .release pid => liftWGObserver (hooks.peerRelease (some pid))
  | .handshake => liftWGObserver (Driver.handshakeObserved hooks)

inductive Label where
  | iteration (activation : Activation)
  | encrypt
  | encryptTail (item : Option (List SkbId))
  | tx (pid : PeerId)
  | decrypt
  | receive
  | ahead (pid : PeerId)
  | aheadPrefix (pid : PeerId)
  | aheadFinish (pid : PeerId) (selected : Activation) (result : IterResult)
  | resched (worker : Worker) (site : Decision)

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (token : Native action) : Shape (liftPrefix action)
  | child (token : Child) : Shape token.action
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value)) : Shape (body >>= next)
  | marked (label : Label) (body : Shape action) : Shape action

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Iteration.Points
