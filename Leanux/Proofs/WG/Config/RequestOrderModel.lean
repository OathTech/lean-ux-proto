import Leanux.Proofs.WG.Campaign2.View
import Leanux.WG.Netlink

/-! Projected request receipts, ordered phase and peer-command languages, and entry-effect data. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG

inductive Kind where
  | updateEntry (flags : UInt32)
  | clearSource (pid : PeerId)
  | port (value : Nat)
  | replacement
  | keyStage
  | peer (attrs : PeerAttrs)

structure Receipt where
  kind : Kind
  result : Int
  before : Campaign2.Snapshot
  after : Campaign2.Snapshot

/-- A complete initial segment of parsed peer commands, all of which returned
nonnegative values. The input suffix is the actual unvisited suffix. -/
inductive PeerPrefix : List PeerEntry → List PeerEntry → List Receipt → Prop
  | nil (xs) : PeerPrefix xs xs []
  | cons {p xs rest r rs}
      (kind : r.kind = .peer p) (nonnegative : 0 ≤ r.result)
      (tail : PeerPrefix xs rest rs) :
      PeerPrefix (.attrs p :: xs) rest (r :: rs)

/-- The completed part of a peer loop on any outcome. The final receipt may
be negative; in that case no later peer command has completed. -/
def PeerPartial (xs : List PeerEntry) (rs : List Receipt) : Prop :=
  (∃ rest, PeerPrefix xs rest rs) ∨
  ∃ before p tail r, PeerPrefix xs (.attrs p :: tail) before ∧
    r.kind = .peer p ∧ r.result < 0 ∧ rs = before ++ [r]

/-- Normal completion distinguishes exhaustion, parse rejection and the first
negative peer return. -/
def PeerFinished (xs : List PeerEntry) (rs : List Receipt) (ret : Int) : Prop :=
  (ret = 0 ∧ PeerPrefix xs [] rs) ∨
  (ret = -EINVAL ∧ ∃ tail, PeerPrefix xs (.malformed :: tail) rs) ∨
  ∃ before p tail r, PeerPrefix xs (.attrs p :: tail) before ∧
    r.kind = .peer p ∧ r.result < 0 ∧ rs = before ++ [r] ∧ ret = r.result

def peerEntry (r : Receipt) : PeerEntry :=
  match r.kind with | .peer p => .attrs p | _ => .malformed

def PeerSafe (xs : List PeerEntry) (h0 h : List Receipt) : Prop :=
  ∃ rs, h = h0 ++ rs ∧ PeerPartial xs rs

def PeerAt (xs rest : List PeerEntry) (h0 : List Receipt)
    (out : Option Int × Unit) (h : List Receipt) : Prop :=
  out.1 = none ∧ ∃ rs, h = h0 ++ rs ∧ PeerPrefix xs rest rs

def PeerDone (xs : List PeerEntry) (h0 : List Receipt)
    (out : Option Int × Unit) (h : List Receipt) : Prop :=
  ∃ rs, h = h0 ++ rs ∧ match out.1 with
    | none => PeerPrefix xs [] rs
    | some ret => PeerFinished xs rs ret

def AfterPeer (xs : List PeerEntry) (p : PeerAttrs) (rest : List PeerEntry)
    (h0 : List Receipt) (ret : Int) (h : List Receipt) : Prop :=
  ∃ prior r, h = h0 ++ (prior ++ [r]) ∧ PeerPrefix xs (.attrs p :: rest) prior ∧
    r.kind = .peer p ∧ r.result = ret

structure Language (α : Type) where
  prefixes : List Receipt → Prop
  normal : α → List Receipt → Prop

def Segment (P : List Receipt → Prop) (before after : List Receipt) : Prop :=
  ∃ added, after = before ++ added ∧ P added

def Language.bind {α β : Type} (A : Language α) (B : α → Language β) : Language β where
  prefixes h := A.prefixes h ∨ ∃ x left right,
    A.normal x left ∧ (B x).prefixes right ∧ h = left ++ right
  normal y h := ∃ x left right,
    A.normal x left ∧ (B x).normal y right ∧ h = left ++ right

def Language.event (kind : Kind) : Language Int where
  prefixes h := h = [] ∨ ∃ r, h = [r] ∧ r.kind = kind
  normal ret h := ∃ r, h = [r] ∧ r.kind = kind ∧ r.result = ret

def Language.peers (attrs : DeviceAttrs) : Language Int :=
  ⟨PeerPartial (attrs.peers.getD []),fun ret rs => PeerFinished (attrs.peers.getD []) rs ret⟩

def Language.returning {α : Type} (x : α) : Language α where
  prefixes h := h = []
  normal y h := y = x ∧ h = []

def Language.closed {α : Type} (P : List Receipt → Prop) : Language α :=
  ⟨P,fun _ => P⟩

def keyedLanguage (attrs : DeviceAttrs) : Language Int :=
  (Language.event .keyStage).bind (fun _ => Language.peers attrs)

def afterPortLanguage (attrs : DeviceAttrs) (flags : UInt32) : Language Int :=
  if flags &&& WGDEVICE_F_REPLACE_PEERS != 0 then
    (Language.event .replacement).bind (fun _ => keyedLanguage attrs)
  else keyedLanguage attrs

def afterFwmarkLanguage (attrs : DeviceAttrs) (flags : UInt32) : Language Int :=
  if attrs.listenPort.isSome then
    (Language.event (.port (attrs.listenPort.getD 0))).bind (fun ret =>
      if ret != 0 then Language.returning ret else afterPortLanguage attrs flags)
  else afterPortLanguage attrs flags

def ClearPrefix (attrs : DeviceAttrs) (h : List Receipt) : Prop :=
  (∀ r ∈ h, ∃ pid, r.kind = .clearSource pid) ∧
  (attrs.fwmark.isSome = false → h = [])

def updateLanguage (attrs : DeviceAttrs) (flags : UInt32) : Language Int :=
  (Language.closed (α := Unit) (ClearPrefix attrs)).bind (fun _ => afterFwmarkLanguage attrs flags)

def acceptedLanguage (attrs : DeviceAttrs) : Language Int :=
  (Language.event (.updateEntry (attrs.flags.getD 0))).bind
    (fun _ => updateLanguage attrs (attrs.flags.getD 0))

/-- The empty normal history is a rejected validation path. An accepted path
records the completed generation increment after validation, before fwmark/port and subsequent stages. -/
def requestLanguage (attrs : DeviceAttrs) : Language Int where
  prefixes h := (acceptedLanguage attrs).prefixes h
  normal ret h := h = [] ∨ (acceptedLanguage attrs).normal ret h

structure Inspection where
  outcome : Campaign2.Outcome Int
  receipts : List Receipt

def peerReceipts (h : List Receipt) : List Receipt :=
  h.filter (fun r => match r.kind with | .peer _ => true | _ => false)

def PeerSilent {α : Type} (L : Language α) : Prop :=
  (∀ h, L.prefixes h → peerReceipts h = []) ∧
    ∀ ret h, L.normal ret h → peerReceipts h = []

def PeerOrdered {α : Type} (attrs : DeviceAttrs) (L : Language α) : Prop :=
  ∀ h, L.prefixes h → PeerPartial (attrs.peers.getD []) (peerReceipts h)

/-- Exact state effect of the accepted update entry. Absence stays absence:
the mirror's modifyDev is a map, not a residency assertion. -/
def incrementState (s : Campaign2.State) : Campaign2.State :=
  {s with device := s.device.map fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1}}

def EntryReceipt (attrs : DeviceAttrs) (initial : Campaign2.State) (r : Receipt) : Prop :=
  r.kind = .updateEntry (attrs.flags.getD 0) ∧ r.result = 0 ∧
    r.before.wg = initial ∧ r.after = {r.before with wg := incrementState r.before.wg}

def Begun (attrs : DeviceAttrs) (initial : Campaign2.State) (h : List Receipt) : Prop :=
  ∃ r rest, h = r :: rest ∧ EntryReceipt attrs initial r

def PreludeSafe (attrs : DeviceAttrs) (initial : Campaign2.State) (h : List Receipt) : Prop :=
  h = [] ∨ Begun attrs initial h

/-- Initial-to-entry linkage on every outcome. On a normal validation-rejection
path the native WG state is unchanged. No final snapshot is asserted on Stop. -/
def PreludeFacts (attrs : DeviceAttrs) (entry : Campaign2.Snapshot) (result : Inspection) : Prop :=
  PreludeSafe attrs entry.wg result.receipts ∧
    match result.outcome with
    | .error _ => True
    | .ok (_,final) => result.receipts = [] → final.wg = entry.wg

end Leanux.Proofs.WG.Config.RequestOrder
