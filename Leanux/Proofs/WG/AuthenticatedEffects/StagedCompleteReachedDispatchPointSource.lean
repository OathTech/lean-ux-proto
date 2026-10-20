import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerPointCoverage
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchStoreSource

/-! Fixed dispatch syntax. Ordinary subsystems are native projection frames;
WireGuard source families are named children, never the dispatch function itself.
The declaration indexes actions, without introducing a second evaluator. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration TransmitSecurity CausalJournal
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
abbrev History := List Event
abbrev Result (α : Type) := Except Stop (α × World)

inductive Control where
  | mtu (value : Nat)
  | deladdr (family : Nat)
  | delroute (family : Nat) (named : Bool) (dst plen oif kind metric : Nat)
  | addroute (dst plen oif kind metric mtu flags : Nat)
  | addaddr (addr plen : Nat)
  | advance (ticks : Nat)
  | netnsClose

def Control.call : Control → Syscall
  | .mtu n => .wgSetMtu n
  | .deladdr family => .wgDeladdr family
  | .delroute family named dst plen oif kind metric => .wgDelroute family named dst plen oif kind metric
  | .addroute dst plen oif kind metric metricMtu flags => .wgAddroute dst plen oif kind metric metricMtu flags
  | .addaddr addr plen => .wgAddaddr addr plen
  | .advance ticks => .wgAdvance ticks
  | .netnsClose => .wgNetnsClose

inductive Native : {α : Type} → Leanux.M α → Type 1 where
  | stored (source : ProductStore.Shape action) : Native action
  | fs (body : FS.M α) : Native (liftFS body)
  | seccomp (body : Seccomp.M α) : Native (liftSeccomp body)
  | ambient (body : AmbientM α) : Native (liftAmbient body)
  | ambientEdit (f : Ambient → Ambient) : Native (modifyAmbient f)
  | read : Native (get : Leanux.M World)
  | files : Native (getFiles : Leanux.M FilesStruct)
  | task (ref : TaskRef) : Native (getTask ref : Leanux.M Task)
  | nextFile (id : Nat) : Native (modify fun w => {w with fs := {w.fs with nextFile := id}})
  | modifyFiles (f : FilesStruct → FilesStruct) : Native (Leanux.modifyFiles f)
  | control (c : Control) : Native (Leanux.dispatch c.call)
  | observeFront : Native DeliverySource.observeFront
  | observeFinish : Native DeliverySource.observeFinish
  | nlRead (fd : Nat) : Native (liftWG (getNlSock fd))
  | nlWrite (fd : Nat) (sock : NlSock) : Native (liftWG (setNlSock fd sock))

inductive Family where
  | config (attrs : DeviceAttrs)
  | create
  | delete
  | open
  | down
  | transmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts)
  | receive (family port : Nat) (message : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat)
  | flood (count port family : Nat) (messages : List (List UInt8))
  | batch (items : List Env.BatchItem)
  | dumpDevice (ref : DeviceRef)
  | dumpStart (fd : Nat) (ref : DeviceRef)
  | dumpReceive (fd : Nat)
  | idle
  | delivery

def Family.Result : Family → Type
  | .dumpDevice _ => Except Int Lean.Json
  | .dumpStart .. | .idle | .delivery => Unit
  | .dumpReceive _ => Option (List NlMessage)
  | _ => Int

def Family.action (family : Family) : PrefixM Event family.Result :=
  match family with
  | .config attrs => liftWGObserver (Driver.configDevice hooks attrs)
  | .create => Driver.dispatchCreateObserved
  | .delete => Driver.dispatchDeleteObserved hooks
  | .open => Driver.envUpObserved hooks
  | .down => Driver.envDownObserved hooks
  | .transmit family addr payload opts => Driver.syscallXmitObserved hooks family addr payload opts
  | .receive family port message tos ll dest => Driver.injectObserved hooks family port message tos ll dest
  | .flood count port family messages => Driver.floodObserved hooks count port family messages
  | .batch items => Driver.batchObserved hooks items
  | .dumpDevice ref => liftWGObserver (RetirementSecurity.NestedPeerRelease.dumpDeviceWith (Driver.nestedOps hooks) ref)
  | .dumpStart fd ref => liftWGObserver (RetirementSecurity.NestedPeerRelease.dumpStartWith (Driver.nestedOps hooks) fd ref)
  | .dumpReceive fd => liftWGObserver (RetirementSecurity.NestedPeerRelease.dumpReceiveWith (Driver.nestedOps hooks) fd)
  | .idle => Driver.idleTimersObserved hooks
  | .delivery => hooks.deliver

inductive Child : {α : Type} → PrefixM Event α → Type 1 where
  | family (source : Family) : Child source.action

inductive Label where
  | syscall (call : Syscall)
  | socket (fd : Nat)
  | netlink
  | observation
  | dump (call : Syscall)

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (token : Native action) : Shape (liftPrefix action)
  | child (token : Child action) : Shape action
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀value,Shape (next value)) : Shape (body >>= next)
  | marked (label : Label) (body : Shape action) : Shape action

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
