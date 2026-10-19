import Leanux.Proofs.WG.Roaming.PollEndpointSource
import Leanux.Proofs.WG.Roaming.PollCallbackSource
import Leanux.Proofs.WG.Queues.NapiSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollHookRules
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
theorem step_factor (pid budget n state) (toStack : List (List UInt8) → Leanux.M Unit) :
    pollStep pid budget toStack n state =
      stepWith (fun {_} a=>a) (fun p pkt ep=>liftWG (consumeDataDone p pkt ep))
        (napiGroReceive toStack) pid budget n state := by
  first
  | rfl
  | unfold pollStep stepWith
    simp only [bind_assoc]
    try rfl
theorem finish_factor (pid budget state) (toStack : List (List UInt8) → Leanux.M Unit) :
    pollFinish pid budget toStack state =
      finishWith (fun {_} a=>a) (napiGroFlushAll toStack) pid budget state := by
  first
  | rfl
  | unfold pollFinish finishWith
    simp only [bind_assoc]
    try rfl
theorem poll_factor (pid budget) (toStack : List (List UInt8) → Leanux.M Unit) :
    rxPoll pid budget toStack =
      pollWith (fun {_} a=>a) (fun p pkt ep=>liftWG (consumeDataDone p pkt ep))
        (napiGroReceive toStack) (napiGroFlushAll toStack) pid budget := by
  rw [rxPoll_source]
  have stepEq : pollStep pid budget toStack = stepWith (fun {_} a=>a)
      (fun p pkt ep=>liftWG (consumeDataDone p pkt ep)) (napiGroReceive toStack) pid budget :=
    funext (fun n=>funext (fun state=>step_factor pid budget n state toStack))
  simp only [pollWith,stepEq,finish_factor]

end Leanux.Proofs.WG.Roaming.PollHookRules
namespace Leanux.Proofs.WG.TimerDiscipline.ReceiveHookPoll
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Roaming
variable {E : Type}

def pollWith (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (stack : List (List UInt8) → PrefixM E Unit) (pid : PeerId) (budget : Nat) : PrefixM E Nat :=
  PollHookRules.pollWith (fun {_} action=>liftPrefix action) consume
    (napiGroReceivePrefix stack) (napiGroFlushAllPrefix stack) pid budget
def softirqWith (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (stack : List (List UInt8) → PrefixM E Unit) : PrefixM E Unit :=
  RxNapi.softirqWith (liftPrefix (liftWG RxNapi.pendingSource)) (pollWith consume stack)
def inlineWith (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (stack : List (List UInt8) → PrefixM E Unit) : PrefixM E Unit :=
  RxNapi.inlineWith (liftPrefix (liftWG RxNapi.pendingSource)) (pollWith consume stack)
def irqExitWith (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (stack : List (List UInt8) → PrefixM E Unit) : PrefixM E Unit :=
  RxNapi.irqExitWith (liftPrefix (liftWG RxNapi.scheduledSource)) (softirqWith consume stack)

variable (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (stack : List (List UInt8) → PrefixM E Unit)
    (hc : ∀ p pkt ep, ErasesPrefix (consume p pkt ep) (liftWG (consumeDataDone p pkt ep)))
    (hs : ∀ packets, ErasesPrefix (stack packets) (packets.forM Leanux.Env.deliverInner))
include hc hs
theorem pollWith_erases (pid budget) :
    ErasesPrefix (pollWith consume stack pid budget)
      (rxPoll pid budget (fun packets=>packets.forM Leanux.Env.deliverInner)) :=
  by
    rw [PollHookRules.poll_factor]
    exact PollHookRules.poll_erases consume stack _ hc hs pid budget
theorem softirqWith_erases : ErasesPrefix (softirqWith consume stack) Leanux.Env.napiSoftirq :=
  RxNapi.softirq_erases (erasesPrefix_lift _) (pollWith_erases consume stack hc hs)
theorem inlineWith_erases : ErasesPrefix (inlineWith consume stack) Leanux.Env.pollScheduledInline :=
  RxNapi.inline_erases (erasesPrefix_lift _) (pollWith_erases consume stack hc hs)
theorem irqExitWith_erases : ErasesPrefix (irqExitWith consume stack) Leanux.Env.napiIrqExit :=
  RxNapi.irqExit_erases (erasesPrefix_lift _) (softirqWith_erases consume stack hc hs)
omit hc hs

variable (S : List E → Prop)
    (cv : ∀ p pkt ep, PrefixPreserves (fun h _=>S h) S (consume p pkt ep))
    (sv : ∀ packets, PrefixPreserves (fun h _=>S h) S (stack packets))
include cv sv
theorem pollWith_valid (pid budget) :
    PrefixPreserves (fun h _=>S h) S (pollWith consume stack pid budget) :=
  PollHookRules.poll_preserves S consume stack cv sv pid budget
theorem softirqWith_valid :
    PrefixPreserves (fun h _=>S h) S (softirqWith consume stack) :=
  RxNapi.softirq_preserves
    (fun (h : List E) (_ : World) (pre : S h)=>pre) (fun _ _ _ _ pre=>pre)
    (PollHookRules.lift_safe S _) (pollWith_valid consume stack S cv sv)
theorem inlineWith_valid :
    PrefixPreserves (fun h _=>S h) S (inlineWith consume stack) :=
  RxNapi.inline_preserves
    (fun (h : List E) (_ : World) (pre : S h)=>pre) (fun _ _ _ _ pre=>pre)
    (PollHookRules.lift_safe S _) (pollWith_valid consume stack S cv sv)
theorem irqExitWith_valid :
    PrefixPreserves (fun h _=>S h) S (irqExitWith consume stack) :=
  RxNapi.irqExit_preserves
    (fun (h : List E) (_ : World) (pre : S h)=>pre) (fun _ _ _ _ pre=>pre)
    (PollHookRules.lift_safe S _) (softirqWith_valid consume stack S cv sv)
omit cv sv

variable (ca : ∀ p pkt ep, Appends (consume p pkt ep))
    (sa : ∀ packets, Appends (stack packets))
include ca sa
theorem pollWith_appends (pid budget) : Appends (pollWith consume stack pid budget) :=
  PollHookRules.poll_appends consume stack ca sa pid budget
theorem softirqWith_appends : Appends (softirqWith consume stack) :=
  NapiSource.softirq_appends (Appends.lift _) (pollWith_appends consume stack ca sa)
theorem inlineWith_appends : Appends (inlineWith consume stack) :=
  NapiSource.inline_appends (Appends.lift _) (pollWith_appends consume stack ca sa)
theorem irqExitWith_appends : Appends (irqExitWith consume stack) :=
  NapiSource.irqExit_appends (Appends.lift _) (softirqWith_appends consume stack ca sa)
omit ca sa
end Leanux.Proofs.WG.TimerDiscipline.ReceiveHookPoll
