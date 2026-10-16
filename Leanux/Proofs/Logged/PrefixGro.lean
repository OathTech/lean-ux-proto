import Leanux.Proofs.Logged.PrefixLoops
import Leanux.WG.RxData

/-! Failure-retaining GRO callback lifting with original GroState. The callback
may run at batch flushes inside a poll, as well as at its completion. -/
namespace Leanux.Proofs.Logged
open Leanux Leanux.WG
variable {Event : Type} {I : List Event → World → Prop} {S : List Event → Prop}

def groNormalListPrefix (toStack : List (List UInt8) → PrefixM Event Unit) (gro : GroState) : PrefixM Event GroState := do
  if gro.rxCount == 0 then return gro
  toStack gro.rxList
  return { gro with rxList := [], rxCount := 0 }

def groNormalOnePrefix (toStack : List (List UInt8) → PrefixM Event Unit) (gro : GroState)
    (pkt : List UInt8) (segs : Nat) : PrefixM Event GroState := do
  let gro := { gro with rxList := gro.rxList ++ [pkt], rxCount := gro.rxCount + segs }
  if gro.rxCount ≥ GRO_NORMAL_BATCH then groNormalListPrefix toStack gro else return gro

def napiGroReceivePrefix (toStack : List (List UInt8) → PrefixM Event Unit) (gro : GroState)
    (pkt : List UInt8) : PrefixM Event GroState := do
  if groTakenAtOnce pkt then groNormalOnePrefix toStack gro pkt 1
  else
    if !gro.held.isEmpty then liftPrefix (unsupported "GRO holds a second TCP segment in one poll (coalescing, or the hash buckets' flush order)")
    return { gro with held := gro.held ++ [pkt] }

def napiGroFlushAllPrefix (toStack : List (List UInt8) → PrefixM Event Unit) (gro : GroState) : PrefixM Event Unit := do
  let mut g := gro
  for pkt in gro.held do g ← groNormalOnePrefix toStack g pkt 1
  g := { g with held := [] }
  _ ← groNormalListPrefix toStack g

theorem groNormalListPrefix_erases
    (logged : List (List UInt8) → PrefixM Event Unit) (original : List (List UInt8) → M Unit)
    (h : ∀ packets, ErasesPrefix (logged packets) (original packets)) (gro : GroState) :
    ErasesPrefix (groNormalListPrefix logged gro) (groNormalList original gro) := by
  unfold groNormalListPrefix groNormalList
  split
  · exact erasesPrefix_pure _
  · exact erasesPrefix_bind (h _) (fun _ => erasesPrefix_pure _)

theorem groNormalOnePrefix_erases
    (logged : List (List UInt8) → PrefixM Event Unit) (original : List (List UInt8) → M Unit)
    (h : ∀ packets, ErasesPrefix (logged packets) (original packets))
    (gro : GroState) (pkt : List UInt8) (segs : Nat) :
    ErasesPrefix (groNormalOnePrefix logged gro pkt segs) (groNormalOne original gro pkt segs) := by
  unfold groNormalOnePrefix groNormalOne
  dsimp only
  split
  · exact groNormalListPrefix_erases logged original h _
  · exact erasesPrefix_pure _

theorem napiGroReceivePrefix_erases
    (logged : List (List UInt8) → PrefixM Event Unit) (original : List (List UInt8) → M Unit)
    (h : ∀ packets, ErasesPrefix (logged packets) (original packets))
    (gro : GroState) (pkt : List UInt8) :
    ErasesPrefix (napiGroReceivePrefix logged gro pkt) (napiGroReceive original gro pkt) := by
  unfold napiGroReceivePrefix napiGroReceive
  split
  · exact groNormalOnePrefix_erases logged original h _ _ _
  · split
    · exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_pure _)
    · exact erasesPrefix_pure _

theorem napiGroFlushAllPrefix_erases
    (logged : List (List UInt8) → PrefixM Event Unit) (original : List (List UInt8) → M Unit)
    (h : ∀ packets, ErasesPrefix (logged packets) (original packets)) (gro : GroState) :
    ErasesPrefix (napiGroFlushAllPrefix logged gro) (napiGroFlushAll original gro) := by
  unfold napiGroFlushAllPrefix napiGroFlushAll
  repeat' first
    | with_reducible exact groNormalListPrefix_erases logged original h _
    | with_reducible exact groNormalOnePrefix_erases logged original h _ _ _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_forIn
    | (with_reducible intro x; try dsimp only)

theorem groNormalListPrefix_preserves
    (callback : List (List UInt8) → PrefixM Event Unit)
    (hs : ∀ h w, I h w → S h)
    (hc : ∀ packets, PrefixPreserves I S (callback packets)) (gro : GroState) :
    PrefixPreserves I S (groNormalListPrefix callback gro) := by
  unfold groNormalListPrefix
  repeat' first
    | with_reducible exact hc _
    | with_reducible exact PrefixPreserves.pure hs _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | with_reducible apply PrefixPreserves.forIn _ _ _ hs
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem groNormalOnePrefix_preserves
    (callback : List (List UInt8) → PrefixM Event Unit)
    (hs : ∀ h w, I h w → S h)
    (hc : ∀ packets, PrefixPreserves I S (callback packets)) (gro : GroState) (pkt : List UInt8) (segs : Nat) :
    PrefixPreserves I S (groNormalOnePrefix callback gro pkt segs) := by
  unfold groNormalOnePrefix
  repeat' first
    | with_reducible exact groNormalListPrefix_preserves callback hs hc _
    | with_reducible exact hc _
    | with_reducible exact PrefixPreserves.pure hs _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | with_reducible apply PrefixPreserves.forIn _ _ _ hs
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem napiGroReceivePrefix_preserves
    (callback : List (List UInt8) → PrefixM Event Unit)
    (hs : ∀ h w, I h w → S h)
    (hc : ∀ packets, PrefixPreserves I S (callback packets)) (gro : GroState) (pkt : List UInt8) :
    PrefixPreserves I S (napiGroReceivePrefix callback gro pkt) := by
  unfold napiGroReceivePrefix
  repeat' first
    | with_reducible exact groNormalListPrefix_preserves callback hs hc _
    | with_reducible exact groNormalOnePrefix_preserves callback hs hc _ _ _
    | with_reducible exact hc _
    | with_reducible exact PrefixPreserves.pure hs _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | with_reducible apply PrefixPreserves.forIn _ _ _ hs
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ hs
  intro h w x v hi hr
  change (Except.error _ : Except Stop _) = _ at hr
  cases hr

theorem napiGroFlushAllPrefix_preserves
    (callback : List (List UInt8) → PrefixM Event Unit)
    (hs : ∀ h w, I h w → S h)
    (hc : ∀ packets, PrefixPreserves I S (callback packets)) (gro : GroState) :
    PrefixPreserves I S (napiGroFlushAllPrefix callback gro) := by
  unfold napiGroFlushAllPrefix
  repeat' first
    | with_reducible exact groNormalListPrefix_preserves callback hs hc _
    | with_reducible exact groNormalOnePrefix_preserves callback hs hc _ _ _
    | with_reducible exact hc _
    | with_reducible exact PrefixPreserves.pure hs _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | with_reducible apply PrefixPreserves.forIn _ _ _ hs
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

end Leanux.Proofs.Logged
