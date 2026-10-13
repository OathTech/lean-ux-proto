import Leanux.Proofs.WG.Queues.GroCallback

/-! Tags follow the original GRO state and every batch/held flush. Erasure
requires no validity of the supplied lists or segment count. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Logged

structure TaggedGro where
  rxList : List GroEntry := []
  rxCount : Nat := 0
  held : List GroEntry := []

def TaggedGro.erase (g : TaggedGro) : GroState :=
  ⟨g.rxList.map GroEntry.bytes, g.rxCount, g.held.map GroEntry.bytes⟩

def groNormalListTagged (g : TaggedGro) : PrefixM GroEvent TaggedGro := do
  if g.rxCount == 0 then return g
  flushGro g.rxList
  return {g with rxList := [], rxCount := 0}

def groNormalOneTagged (g : TaggedGro) (entry : GroEntry) (segs : Nat) : PrefixM GroEvent TaggedGro := do
  let g := {g with rxList := g.rxList ++ [entry], rxCount := g.rxCount + segs}
  if g.rxCount ≥ GRO_NORMAL_BATCH then groNormalListTagged g else return g

def napiGroReceiveTagged (g : TaggedGro) (entry : GroEntry) : PrefixM GroEvent TaggedGro := do
  if groTakenAtOnce entry.bytes then groNormalOneTagged g entry 1
  else
    if !g.held.isEmpty then
      liftPrefix (unsupported "GRO holds a second TCP segment in one poll (coalescing, or the hash buckets' flush order)")
    return {g with held := g.held ++ [entry]}

def napiGroFlushAllTagged (gro : TaggedGro) : PrefixM GroEvent Unit := do
  let mut g := gro
  for entry in gro.held do g ← groNormalOneTagged g entry 1
  g := {g with held := []}
  _ ← groNormalListTagged g

theorem groNormalListTagged_erases (g : TaggedGro) :
    ErasesTo TaggedGro.erase (groNormalListTagged g)
      (groNormalList (fun bytes => bytes.forM Leanux.Env.deliverInner) g.erase) := by
  unfold groNormalListTagged groNormalList
  dsimp only [TaggedGro.erase]
  apply erasesTo_ite
  all_goals intro h
  · exact erasesTo_pure TaggedGro.erase _
  · exact erasesTo_bind id TaggedGro.erase (ErasesPrefix.to_projected (flushGro_erases _))
      (fun _ => erasesTo_pure TaggedGro.erase _)

theorem groNormalOneTagged_erases (g : TaggedGro) (e : GroEntry) (segs : Nat) :
    ErasesTo TaggedGro.erase (groNormalOneTagged g e segs)
      (groNormalOne (fun bytes => bytes.forM Leanux.Env.deliverInner) g.erase e.bytes segs) := by
  unfold groNormalOneTagged groNormalOne
  dsimp only [TaggedGro.erase]
  split
  · simpa [TaggedGro.erase, List.map_append] using
      groNormalListTagged_erases {g with rxList := g.rxList ++ [e], rxCount := g.rxCount + segs}
  · simpa [TaggedGro.erase, List.map_append] using
      erasesTo_pure TaggedGro.erase {g with rxList := g.rxList ++ [e], rxCount := g.rxCount + segs}

theorem napiGroReceiveTagged_erases (g : TaggedGro) (e : GroEntry) :
    ErasesTo TaggedGro.erase (napiGroReceiveTagged g e)
      (napiGroReceive (fun bytes => bytes.forM Leanux.Env.deliverInner) g.erase e.bytes) := by
  unfold napiGroReceiveTagged napiGroReceive
  simp only [TaggedGro.erase, List.isEmpty_map]
  split
  · exact groNormalOneTagged_erases g e 1
  · split
    · apply erasesTo_bind id TaggedGro.erase (ErasesPrefix.to_projected (erasesPrefix_lift _))
      intro _
      simpa [TaggedGro.erase, List.map_append] using
        erasesTo_pure TaggedGro.erase {g with held := g.held ++ [e]}
    · simpa [TaggedGro.erase, List.map_append] using
        erasesTo_pure TaggedGro.erase {g with held := g.held ++ [e]}

theorem napiGroFlushAllTagged_erases (gro : TaggedGro) :
    ErasesPrefix (napiGroFlushAllTagged gro)
      (napiGroFlushAll (fun bytes => bytes.forM Leanux.Env.deliverInner) gro.erase) := by
  apply ErasesTo.identity
  unfold napiGroFlushAllTagged napiGroFlushAll
  apply erasesTo_bind TaggedGro.erase id
  · apply erasesTo_forIn_map TaggedGro.erase GroEntry.bytes
    intro e g
    exact erasesTo_bind TaggedGro.erase (projectStep TaggedGro.erase)
      (groNormalOneTagged_erases g e 1) (fun g => erasesTo_pure (projectStep TaggedGro.erase) (.yield g))
  · intro g
    apply erasesTo_bind TaggedGro.erase id (groNormalListTagged_erases {g with held := []})
    intro _
    exact erasesTo_pure id ()

/-- A held packet followed by a normal packet is handed to the callback in
normal-then-held order. This is a helper equation, not a scheduler witness. -/
theorem held_then_normal (callback : List (List UInt8) → M Unit) (held normal : List UInt8)
    (hh : groTakenAtOnce held = false) (hn : groTakenAtOnce normal = true) :
    (do let g ← napiGroReceive callback {} held
        let g ← napiGroReceive callback g normal
        napiGroFlushAll callback g) = callback [normal, held] := by
  simp [napiGroReceive, hh, hn, groNormalOne, groNormalList, napiGroFlushAll,
    GRO_NORMAL_BATCH, List.forIn_cons, List.forIn_nil]

end Leanux.Proofs.WG.Queues
