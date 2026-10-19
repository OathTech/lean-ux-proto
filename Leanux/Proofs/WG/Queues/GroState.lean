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
  match groNetwork entry.bytes with
  | none => groNormalOneTagged g entry 1
  | some (off, lengthFlush) =>
    match groTcpHeader entry.bytes off with
    | none => groNormalOneTagged g entry 1
    | some (thlen, len) =>
      let flags := (entry.bytes.getD (off + 13) 0).toNat
      match g.held with
      | [held] =>
        if groSameFlow held.bytes entry.bytes off then
          if !groMergeRefused held.bytes entry.bytes off thlen len then
            liftPrefix (unsupported "GRO coalesces two segments of one flow in one poll (skb_gro_receive)")
          let g ← groNormalOneTagged {g with held := []} held 1
          if lengthFlush || groFinalFlush flags len then groNormalOneTagged g entry 1
          else return {g with held := [entry]}
        else
          if lengthFlush || groFinalFlush flags len then groNormalOneTagged g entry 1
          else liftPrefix (unsupported "GRO holds a second TCP segment in one poll (the hash buckets' flush order)")
      | _ =>
        if lengthFlush || groFinalFlush flags len then groNormalOneTagged g entry 1
        else return {g with held := g.held ++ [entry]}

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
  have pure_eq (g : TaggedGro) (a : GroState) (he : g.erase = a) :
      ErasesTo TaggedGro.erase (pure g : PrefixM GroEvent TaggedGro) (pure a) := by
    rw [← he]
    exact erasesTo_pure TaggedGro.erase g
  rcases g with ⟨xs, count, held⟩
  cases held <;> try (rename_i old rest; cases rest)
  all_goals
    unfold napiGroReceiveTagged napiGroReceive
    simp only [TaggedGro.erase, List.map_cons, List.map_nil]
    repeat' first
      | contradiction
      | with_reducible exact groNormalOneTagged_erases _ _ _
      | (with_reducible exact erasesTo_pure TaggedGro.erase _)
      | with_reducible exact ErasesPrefix.to_projected (erasesPrefix_lift _)
      | with_reducible apply erasesTo_ite
      | with_reducible apply erasesTo_bind TaggedGro.erase TaggedGro.erase
      | with_reducible apply erasesTo_bind id TaggedGro.erase
      | (with_reducible intro x; try dsimp only)
      | (split <;> simp_all only)
    all_goals first
      | exact groNormalOneTagged_erases _ _ _
      | (apply pure_eq; simp only [TaggedGro.erase, List.map_append, List.map_cons, List.map_nil])
      | exact fun _ _ => rfl

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

/-- Whether a lone packet passes immediately to GRO's normal list. This reads
the mirror's network/header/final-flush tests, including zero payload. -/
def groTakesAlone (pkt : List UInt8) : Bool :=
  match groNetwork pkt with
  | none => true
  | some (off, lengthFlush) =>
    match groTcpHeader pkt off with
    | none => true
    | some (_, len) => lengthFlush || groFinalFlush (pkt.getD (off + 13) 0).toNat len

/-- A packet bypasses a held segment when it exits before TCP flow lookup,
or the lookup finds a different flow. Same-flow refusal does not bypass it. -/
def groBypassesHeld (held pkt : List UInt8) : Bool :=
  match groNetwork pkt with
  | none => true
  | some (off, _) =>
    match groTcpHeader pkt off with
    | none => true
    | some _ => !groSameFlow held pkt off

/-- A held packet followed by an independently flushing packet that bypasses
it reaches the callback in reverse order. The bypass premise is essential:
same-flow refusal completes the held segment first. -/
theorem held_then_normal (callback : List (List UInt8) → Leanux.M Unit)
    (held normal : List UInt8) (hh : groTakesAlone held = false)
    (hn : groTakesAlone normal = true) (hb : groBypassesHeld held normal = true) :
    (do let g ← napiGroReceive callback {} held
        let g ← napiGroReceive callback g normal
        napiGroFlushAll callback g) = callback [normal, held] := by
  cases hnet : groNetwork held with
  | none => simp [groTakesAlone, hnet] at hh
  | some net =>
    rcases net with ⟨off, lengthFlush⟩
    cases htcp : groTcpHeader held off with
    | none => simp [groTakesAlone, hnet, htcp] at hh
    | some tcp =>
      rcases tcp with ⟨thlen, len⟩
      simp only [groTakesAlone, hnet, htcp] at hh
      have first : napiGroReceive callback {} held = pure { held := [held] } := by
        simp_all [napiGroReceive]
      rw [first]
      simp only [pure_bind]
      cases nnet : groNetwork normal with
      | none =>
        simp [napiGroReceive, nnet, groNormalOne, groNormalList, napiGroFlushAll, GRO_NORMAL_BATCH]
      | some net =>
        rcases net with ⟨noff, nflush⟩
        cases ntcp : groTcpHeader normal noff with
        | none =>
          simp [napiGroReceive, nnet, ntcp, groNormalOne, groNormalList, napiGroFlushAll, GRO_NORMAL_BATCH]
        | some tcp =>
          rcases tcp with ⟨nthlen, nlen⟩
          simp only [groTakesAlone, nnet, ntcp] at hn
          simp only [groBypassesHeld, nnet, ntcp] at hb
          simp_all [napiGroReceive, groNormalOne, groNormalList, napiGroFlushAll, GRO_NORMAL_BATCH]

end Leanux.Proofs.WG.Queues
