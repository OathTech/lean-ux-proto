import Leanux.Proofs.WG.AuthenticatedEffects.Emission
import Leanux.Proofs.WG.AuthenticatedEffects.NonceSize

/-! A receipt is emitted after the actual native tunnel append. The append is
last in the source, so every earlier Stop retains the incoming receipt prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.Framing

structure DatagramReceipt where
  endpoint : Endpoint
  bytes : List UInt8
  ds : Nat
  route : Route
  front : WGRunWitness Nat

def DatagramReceipt.datagram (r : DatagramReceipt) : SentDatagram :=
  tunnelDatagram r.endpoint r.bytes r.ds r.route r.front.value

def DatagramReceipt.after (r : DatagramReceipt) : WGWorld :=
  {r.front.after with sent := r.front.after.sent ++ [r.datagram]}

def DatagramReceipt.Valid (r : DatagramReceipt) : Prop :=
  r.front.Valid (tunnelReplyFront r.endpoint r.bytes r.route)

def tunnelObserved (e : Endpoint) (bytes : List UInt8) (ds : Nat) (route : Route) :
    WGPrefix DatagramReceipt Unit := do
  let front ← captureWGRun (tunnelReplyFront e bytes route)
  liftWGPrefix (modify fun w => {w with sent := w.sent ++ [tunnelDatagram e bytes ds route front.value]})
  emitStatePrefix ⟨e,bytes,ds,route,front⟩

theorem tunnelObserved_run (e : Endpoint) (bytes : List UInt8) (ds : Nat) (route : Route)
    (w : WGWorld) (a : Ambient) (h : List DatagramReceipt) :
    runWGPrefix (tunnelObserved e bytes ds route) w a h =
      match ((tunnelReplyFront e bytes route).run w).run a with
      | .error err => (.error err,h)
      | .ok ((sport,u),b) =>
        (.ok (((),{u with sent := u.sent ++ [tunnelDatagram e bytes ds route sport]}),b),
          h ++ [⟨e,bytes,ds,route,⟨sport,w,u,a,b⟩⟩]) := by
  unfold tunnelObserved
  change runStatePrefix _ w a h = _
  rw [runStatePrefix_bind]
  have hc := runWGPrefix_captureWGRun (E := DatagramReceipt) (tunnelReplyFront e bytes route) w a h
  change runStatePrefix _ w a h = _ at hc
  rw [hc]
  cases native : ((tunnelReplyFront e bytes route).run w).run a with
  | error err => rfl
  | ok out => rcases out with ⟨⟨sport,u⟩,b⟩; rfl

theorem tunnelObserved_erases (e : Endpoint) (bytes : List UInt8) (ds : Nat) (route : Route) :
    ErasesStatePrefix (tunnelObserved e bytes ds route) (tunnelXmitSource e bytes ds route false) := by
  intro w a h
  change (runWGPrefix (tunnelObserved e bytes ds route) w a h).1 = _
  rw [tunnelObserved_run,tunnelReply_factor,native_bind_run]
  cases native : ((tunnelReplyFront e bytes route).run w).run a with
  | error err => rfl
  | ok out => rcases out with ⟨⟨sport,u⟩,b⟩; rfl

theorem DatagramReceipt.native (r : DatagramReceipt) (valid : r.Valid) :
    ((tunnelXmitSource r.endpoint r.bytes r.ds r.route false).run r.front.before).run r.front.ambientBefore =
      .ok (((),r.after),r.front.ambientAfter) := by
  rw [tunnelReply_factor,native_bind_run]
  change ((tunnelReplyFront r.endpoint r.bytes r.route).run r.front.before).run r.front.ambientBefore = _ at valid
  rw [valid]
  rfl

theorem DatagramReceipt.append (r : DatagramReceipt) (valid : r.Valid) :
    r.after.sent = r.front.before.sent ++ [r.datagram] := by
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (tunnelReplyFront_sent r.endpoint r.bytes r.route)
    r.front.before r.front.ambientBefore r.front.value r.front.after r.front.ambientAfter valid
  change r.front.after.sent ++ [r.datagram] = _
  rw [frame]

theorem tunnelObserved_receipts (e : Endpoint) (bytes : List UInt8) (ds : Nat) (route : Route)
    (w : WGWorld) (a : Ambient) (h : List DatagramReceipt) :
    ∃ suffix, (runWGPrefix (tunnelObserved e bytes ds route) w a h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix,
        r.Valid ∧ r.endpoint = e ∧ r.bytes = bytes ∧ r.ds = ds ∧ r.route = route := by
  rw [tunnelObserved_run]
  cases native : ((tunnelReplyFront e bytes route).run w).run a with
  | error err => exact ⟨[],by simp⟩
  | ok out =>
    rcases out with ⟨⟨sport,u⟩,b⟩
    refine ⟨[⟨e,bytes,ds,route,⟨sport,w,u,a,b⟩⟩],rfl,by simp,?_⟩
    intro receipt mem
    simp only [List.mem_singleton] at mem
    subst receipt
    exact ⟨native,rfl,rfl,rfl,rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects
