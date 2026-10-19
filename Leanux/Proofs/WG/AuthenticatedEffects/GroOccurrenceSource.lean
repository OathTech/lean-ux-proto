import Leanux.Proofs.WG.AuthenticatedEffects.CandidatePollSource
import Leanux.Proofs.Logged.PrefixGro

/-! Proof-side GRO tags follow the actual candidate occurrence through both
the held list and the normal batch. A tag is metadata, not an authentication
claim. In particular, a flush never borrows the currently active candidate's
identity for an older buffered packet. All native GRO refusals remain present. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence
open Leanux Leanux.WG Leanux.Proofs.Logged

structure Entry where
  scope : Nat
  skb : SkbId
  packet : RxPacket
  bytes : List UInt8

def Entry.map (scopeMap : Nat → Nat) (entry : Entry) : Entry :=
  {entry with scope := scopeMap entry.scope}

structure Buffer where
  rxList : List Entry := []
  rxCount : Nat := 0
  held : List Entry := []

def Buffer.erase (buffer : Buffer) : GroState :=
  ⟨buffer.rxList.map Entry.bytes, buffer.rxCount, buffer.held.map Entry.bytes⟩

def Buffer.map (scopeMap : Nat → Nat) (buffer : Buffer) : Buffer :=
  ⟨buffer.rxList.map (Entry.map scopeMap), buffer.rxCount,
    buffer.held.map (Entry.map scopeMap)⟩

def normalListWith {m : Type → Type} [Monad m]
    (toStack : List Entry → m Unit) (gro : Buffer) : m Buffer := do
  if gro.rxCount == 0 then return gro
  toStack gro.rxList
  return {gro with rxList := [], rxCount := 0}

def normalOneWith {m : Type → Type} [Monad m]
    (toStack : List Entry → m Unit) (gro : Buffer) (entry : Entry)
    (segs : Nat) : m Buffer := do
  let gro := {gro with rxList := gro.rxList ++ [entry], rxCount := gro.rxCount + segs}
  if gro.rxCount ≥ GRO_NORMAL_BATCH then normalListWith toStack gro else return gro

def receiveWith {m : Type → Type} [Monad m]
    (step : {α : Type} → Leanux.M α → m α)
    (toStack : List Entry → m Unit) (gro : Buffer) (entry : Entry) : m Buffer := do
  match groNetwork entry.bytes with
  | none => normalOneWith toStack gro entry 1
  | some (off, lengthFlush) =>
    match groTcpHeader entry.bytes off with
    | none => normalOneWith toStack gro entry 1
    | some (thlen, len) =>
      let flags := (entry.bytes.getD (off + 13) 0).toNat
      match gro.held with
      | [held] =>
        if groSameFlow held.bytes entry.bytes off then
          if !groMergeRefused held.bytes entry.bytes off thlen len then
            step (unsupported "GRO coalesces two segments of one flow in one poll (skb_gro_receive)")
          let gro ← normalOneWith toStack {gro with held := []} held 1
          if lengthFlush || groFinalFlush flags len then normalOneWith toStack gro entry 1
          else return {gro with held := [entry]}
        else
          if lengthFlush || groFinalFlush flags len then normalOneWith toStack gro entry 1
          else step (unsupported "GRO holds a second TCP segment in one poll (the hash buckets' flush order)")
      | _ =>
        if lengthFlush || groFinalFlush flags len then normalOneWith toStack gro entry 1
        else return {gro with held := gro.held ++ [entry]}

def flushAllWith {m : Type → Type} [Monad m]
    (toStack : List Entry → m Unit) (gro : Buffer) : m Unit := do
  let mut g := gro
  for entry in gro.held do g ← normalOneWith toStack g entry 1
  g := {g with held := []}
  _ ← normalListWith toStack g

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence
