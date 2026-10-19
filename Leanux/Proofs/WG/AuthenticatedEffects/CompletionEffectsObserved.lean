import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsEmbedding

/-! The joint completion observer preserves every pre-existing receipt and
adds causal timer/work receipts inside the selected completion's scope. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

def focused (encode : Completion.Event → E) (decode : E → Option Completion.Event) : Ops E where
  step := fun a => focusPrefix encode decode (native.step a)
  peer := fun pid => focusPrefix encode decode (native.peer pid)
  modifyPeer := fun pid f => focusPrefix encode decode (native.modifyPeer pid f)
  packet := fun skb => focusPrefix encode decode (native.packet skb)
  completion := fun pid item => focusPrefix encode decode (native.completion pid item)
  send := fun pid skb packet => focusPrefix encode decode (native.send pid skb packet)
  drop := fun pid item => focusPrefix encode decode (native.drop pid item)
  dispose := fun pid item key => focusPrefix encode decode (native.dispose pid item key)
  traversal := fun pid => focusPrefix encode decode (native.traversal pid)
  sent := fun pid => focusPrefix encode decode (native.sent pid)
  dataSent := fun pid => focusPrefix encode decode (native.dataSent pid)
  fresh := fun pid => focusPrefix encode decode (native.fresh pid)

def lifetimeBase (encode : Completion.Event → E) (decode : E → Option Completion.Event) :
    LifetimeEffects.Ops (WGPrefix E) :=
  LifetimeEffects.Ops.focus (encode ∘ lifetimeEvent) (fun e => (decode e).bind lifetime?) LifetimeEffects.native

def observed (encode : Completion.Event → E) (decode : E → Option Completion.Event)
    (scope : E → Option (CausalScope.Event Cause))
    (arm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (queue : TimerEffects.Queued (CausalEffects.Context Cause) → E) : Ops E :=
  let effects := LifetimeEffects.decorate (lifetimeBase encode decode) scope arm queue
  {focused encode decode with
    traversal := fun pid => liftWGObserver (LifetimeEffects.traversalWith effects pid)
    dataSent := fun pid => liftWGObserver (LifetimeEffects.dataSentWith effects pid)
    fresh := fun pid => liftWGObserver (LifetimeEffects.freshWith effects pid)}

def observedStep (encode : Completion.Event → E) (decode : E → Option Completion.Event)
    (recordScope : CausalScope.Event Cause → E) (scope : E → Option (CausalScope.Event Cause))
    (cause : PeerId → List SkbId → Cause)
    (arm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (queue : TimerEffects.Queued (CausalEffects.Context Cause) → E) (pid : PeerId) : PrefixM E Bool :=
  stepScoped recordScope cause (observed encode decode scope arm queue) pid

end Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
