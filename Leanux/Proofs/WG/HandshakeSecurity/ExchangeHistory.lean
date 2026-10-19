import Leanux.Proofs.WG.HandshakeSecurity.ExchangeContracts
import Leanux.Proofs.Logged.NativeCapture

/-! An exchange epoch is the position of its actual successful native start.
History persists across deletion and peer-slot reuse. Native callbacks retain
full run witnesses; no abstract operation can manufacture an accepted edge. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged

inductive Phase where
  | initiationCreated | initiationConsumed | responseCreated | responseConsumed | installed
  deriving DecidableEq

def Phase.tag : Phase → Nat
  | .initiationCreated => HANDSHAKE_CREATED_INITIATION
  | .initiationConsumed => HANDSHAKE_CONSUMED_INITIATION
  | .responseCreated => HANDSHAKE_CREATED_RESPONSE
  | .responseConsumed => HANDSHAKE_CONSUMED_RESPONSE
  | .installed => HANDSHAKE_ZEROED

def Phase.rank : Phase → Nat
  | .initiationCreated | .initiationConsumed => 0
  | .responseCreated | .responseConsumed => 1
  | .installed => 2

structure Entry where
  epoch : Nat
  phase : Phase

def Entry.score (e : Entry) : Nat := 3 * e.epoch + e.phase.rank
abbrev Ledger := PeerId → Option Entry

def Ledger.score (l : Ledger) (pid : PeerId) : Nat := (l pid).elim 0 Entry.score

def set (l : Ledger) (pid : PeerId) (value : Entry) : Ledger :=
  fun target => if target = pid then some value else l target

def advance (l : Ledger) (pid : PeerId) (phase : Phase) : Ledger :=
  fun target => if target = pid then (l pid).map (fun entry => {entry with phase}) else l target

inductive Event where
  | createInitiation (peer : PeerId) (run : WGRunWitness (Option (List UInt8)))
  | consumeInitiation (message : List UInt8) (run : WGRunWitness (Option PeerId))
  | createResponse (peer : PeerId) (run : WGRunWitness (Option (List UInt8)))
  | consumeResponse (message : List UInt8) (run : WGRunWitness (Option PeerId))
  | session (peer : PeerId) (run : WGRunWitness Bool)

def Event.before : Event → WGWorld
  | .createInitiation _ r | .createResponse _ r => r.before
  | .consumeInitiation _ r | .consumeResponse _ r => r.before
  | .session _ r => r.before

def Event.after : Event → WGWorld
  | .createInitiation _ r | .createResponse _ r => r.after
  | .consumeInitiation _ r | .consumeResponse _ r => r.after
  | .session _ r => r.after

def Event.Valid : Event → Prop
  | .createInitiation pid r => r.Valid (WG.createInitiation pid)
  | .consumeInitiation msg r => r.Valid (WG.consumeInitiation msg)
  | .createResponse pid r => r.Valid (WG.createResponse pid)
  | .consumeResponse msg r => r.Valid (WG.consumeResponse msg)
  | .session pid r => r.Valid (beginSession pid)

def Event.peer : Event → Option PeerId
  | .createInitiation pid r | .createResponse pid r => if r.value.isSome then some pid else none
  | .consumeInitiation _ r | .consumeResponse _ r => r.value
  | .session pid r => if r.value then some pid else none

def transition (position : Nat) (l : Ledger) : Event → Ledger
  | .createInitiation pid r => if r.value.isSome then set l pid ⟨position + 1,.initiationCreated⟩ else l
  | .consumeInitiation _ r => match r.value with
    | none => l
    | some pid => set l pid ⟨position + 1,.initiationConsumed⟩
  | .createResponse pid r => if r.value.isSome then advance l pid .responseCreated else l
  | .consumeResponse _ r => match r.value with
    | none => l
    | some pid => advance l pid .responseConsumed
  | .session pid r => if r.value then advance l pid .installed else l

def HasPhase (l : Ledger) (pid : PeerId) (phase : Phase) : Prop :=
  ∃ entry, l pid = some entry ∧ entry.phase = phase

def Allowed (l : Ledger) : Event → Prop
  | .createInitiation _ _ | .consumeInitiation _ _ => True
  | .createResponse pid r => r.value.isSome → HasPhase l pid .initiationConsumed
  | .consumeResponse _ r => ∀ pid, r.value = some pid → HasPhase l pid .initiationCreated
  | .session pid r => r.value = true → HasPhase l pid .responseCreated ∨ HasPhase l pid .responseConsumed

def Bounded (position : Nat) (l : Ledger) : Prop :=
  ∀ pid entry, l pid = some entry → 0 < entry.epoch ∧ entry.epoch ≤ position

def Coherent (l : Ledger) (w : WGWorld) : Prop :=
  ∀ pid tag, handshakeTagAt w pid = some tag → tag ≠ HANDSHAKE_ZEROED →
    ∃ entry, l pid = some entry ∧ entry.phase.tag = tag

inductive History : List Event → Ledger → Prop where
  | nil : History [] (fun _ => none)
  | snoc {h : List Event} {l : Ledger} (prior : History h l) (event : Event)
      (valid : event.Valid) (allowed : Allowed l event) :
      History (h ++ [event]) (transition h.length l event)

def StateInv (h : List Event) (w : WGWorld) : Prop :=
  ∃ ledger, History h ledger ∧ Coherent ledger w

def Safe (h : List Event) : Prop := ∃ ledger, History h ledger

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
