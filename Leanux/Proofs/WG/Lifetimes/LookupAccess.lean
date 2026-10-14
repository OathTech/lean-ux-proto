import Leanux.Proofs.WG.Lifetimes.KeypairRotation
import Leanux.Proofs.Framing.WGIndex

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Reference-taking lookups. Index and public-key table scans inspect scalar
references; every resolved peer access remains explicit, including the read
preceding a zero or overflowing reference count. The retired pending-worker
helper is the original no-op and emits no access. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def requireNotPendingMixed (_pid : PeerId) (_what : String) : MixedM Unit := pure ()

theorem requireNotPendingMixed_erases (pid : PeerId) (what : String) :
    ErasesPrefix (requireNotPendingMixed pid what) (requireNotPending pid what) :=
  erasesPrefix_pure _

theorem requireNotPendingMixed_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (what : String) :
    AmbientSpec I P (requireNotPendingMixed pid what) (fun _ => P) := c.pure P _

def peerGetMaybeZeroPrefix (peer : Option PeerId) : MixedM (Option PeerId) := do
  if ← liftPrefix (branch .peerGetMaybeZeroNull peer.isNone) then return none
  let some pid := peer | liftPrefix (invariant "unreachable")
  requireNotPendingMixed pid "a reference count the handshake worker also changes"
  let p ← getPeerMixed pid
  let live ← liftPrefix (refcountIncNotZero p.refcount)
  if ← liftPrefix (branch .peerGetMaybeZeroDead !live) then return none
  setPeerMixed pid {p with refcount := p.refcount + 1}
  return some pid

theorem peerGetMaybeZeroPrefix_erases (peer : Option PeerId) :
    ErasesPrefix (peerGetMaybeZeroPrefix peer) (peerGetMaybeZero peer) := by
  unfold peerGetMaybeZeroPrefix peerGetMaybeZero
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro isNull
  split
  · exact erasesPrefix_pure _
  · cases peer with
    | none => exact erasesPrefix_lift _
    | some pid =>
      apply erasesPrefix_bind (requireNotPendingMixed_erases pid _)
      intro _
      apply erasesPrefix_bind (getPeerMixed_erases pid)
      intro p
      apply erasesPrefix_bind (erasesPrefix_lift _)
      intro live
      apply erasesPrefix_bind (erasesPrefix_lift _)
      intro dead
      split
      · exact erasesPrefix_pure _
      · exact erasesPrefix_bind (setPeerMixed_erases pid _) (fun _ => erasesPrefix_pure _)

theorem peerGetMaybeZeroPrefix_spec_ambient (c : AmbientContracts I)
    (P : IdentityView → Prop) (peer : Option PeerId) :
    AmbientSpec I P (peerGetMaybeZeroPrefix peer) (fun _ => P) := by
  unfold peerGetMaybeZeroPrefix
  apply PrefixEnsures.bind (c.branch P _ _)
  intro isNull
  split
  · exact c.pure P _
  · cases peer with
    | none => exact c.invariant P _
    | some pid =>
      apply PrefixEnsures.bind (requireNotPendingMixed_spec c P pid _)
      intro _
      apply PrefixEnsures.bind (c.getPeer P pid)
      intro p
      let Q := fun s : IdentityView => P s ∧ s.1.slots pid = some p.internalId
      apply PrefixEnsures.bind (c.kernel Q _ (refcountIncNotZero_sameKernel _))
      intro live
      apply PrefixEnsures.bind (c.branch Q _ _)
      intro dead
      split
      · exact AmbientContracts.forget (c.pure Q none) (fun _ _ hi => hi.1)
      · apply PrefixEnsures.bind (c.setPeer P pid {p with refcount := p.refcount + 1})
        intro _
        exact c.pure P _

def indexLookupPrefix (kinds : List IndexKind) (index : Nat) : MixedM (Option IndexEntry) := do
  let mut entry : Option IndexEntry := none
  let mut stopped := false
  for e in ← liftPrefix (indexBucket index) do
    _ ← liftPrefix (branch .idxWalk true)
    if ← liftPrefix (branch .idxMatch (e.index == index)) then
      if ← liftPrefix (branch .idxTypeMatch (kinds.contains e.kind)) then entry := some e
      stopped := true
      break
  if !stopped then _ ← liftPrefix (branch .idxWalk false)
  if ← liftPrefix (branch .idxFound entry.isSome) then
    let some e := entry | liftPrefix (invariant "unreachable")
    let peer ← peerGetMaybeZeroPrefix (some e.peer)
    if ← liftPrefix (branch .idxPeerAlive peer.isSome) then return entry
  return none

theorem indexLookupPrefix_erases (kinds : List IndexKind) (index : Nat) :
    ErasesPrefix (indexLookupPrefix kinds index) (indexLookup kinds index) := by
  unfold indexLookupPrefix indexLookup
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro bucket
  apply erasesPrefix_bind
  · apply erasesPrefix_forIn
    intro e state
    rcases state with ⟨entry, stopped⟩
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro _
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro same
    split
    · apply erasesPrefix_bind (erasesPrefix_lift _)
      intro kind
      split <;> exact erasesPrefix_pure _
    · exact erasesPrefix_pure _
  · intro state
    rcases state with ⟨entry, stopped⟩
    dsimp only
    have tail : ErasesPrefix
        (do if ← liftPrefix (branch .idxFound entry.isSome) then
              let some e := entry | liftPrefix (invariant "unreachable")
              let peer ← peerGetMaybeZeroPrefix (some e.peer)
              if ← liftPrefix (branch .idxPeerAlive peer.isSome) then return entry
            return none)
        (do if ← branch .idxFound entry.isSome then
              let some e := entry | invariant "unreachable"
              let peer ← peerGetMaybeZero (some e.peer)
              if ← branch .idxPeerAlive peer.isSome then return entry
            return none) := by
      apply erasesPrefix_bind (erasesPrefix_lift _)
      intro found
      split
      · cases entry with
        | none => exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_pure _)
        | some e =>
          apply erasesPrefix_bind (peerGetMaybeZeroPrefix_erases _)
          intro peer
          apply erasesPrefix_bind (erasesPrefix_lift _)
          intro alive
          split <;> exact erasesPrefix_pure _
      · exact erasesPrefix_pure _
    split
    · exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => tail)
    · exact tail

theorem indexBucket_sameKernel (index : Nat) : SameKernel (indexBucket index) :=
  Framing.indexBucket_sameKernel index

theorem indexLookupPrefix_preserves_ambient (c : AmbientContracts I)
    (kinds : List IndexKind) (index : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (indexLookupPrefix kinds index) := by
  unfold indexLookupPrefix
  apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ (indexBucket_sameKernel index)))
  intro bucket
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn (hs := c.safe)
    intro e state
    rcases state with ⟨entry, stopped⟩
    apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro _
    apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro same
    split
    · apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro kind
      split <;> exact PrefixPreserves.pure c.safe _
    · exact PrefixPreserves.pure c.safe _
  · intro state
    rcases state with ⟨entry, stopped⟩
    dsimp only
    have tail : PrefixPreserves I LifetimeEvent.Safe
        (do if ← liftPrefix (branch .idxFound entry.isSome) then
              let some e := entry | liftPrefix (invariant "unreachable")
              let peer ← peerGetMaybeZeroPrefix (some e.peer)
              if ← liftPrefix (branch .idxPeerAlive peer.isSome) then return entry
            return none) := by
      apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro found
      split
      · cases entry with
        | none =>
          apply PrefixPreserves.bind (AmbientContracts.drop (c.invariant (fun _ => True) _))
          intro _
          exact PrefixPreserves.pure c.safe _
        | some e =>
          apply PrefixPreserves.bind (AmbientContracts.drop (peerGetMaybeZeroPrefix_spec_ambient c (fun _ => True) _))
          intro peer
          apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
          intro alive
          split <;> exact PrefixPreserves.pure c.safe _
      · exact PrefixPreserves.pure c.safe _
    split
    · exact PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _)) (fun _ => tail)
    · exact tail

def pubkeyLookupPrefix (key : Key) : MixedM (Option PeerId) := do
  let found := ((← liftPrefix getDev).peerHashtable.find? (·.1 == key)).map (·.2)
  _ ← liftPrefix (branch .pubkeyLookupMatch found.isSome)
  peerGetMaybeZeroPrefix found

theorem pubkeyLookupPrefix_erases (key : Key) :
    ErasesPrefix (pubkeyLookupPrefix key) (pubkeyLookup key) := by
  unfold pubkeyLookupPrefix pubkeyLookup
  exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
    erasesPrefix_bind (erasesPrefix_lift _) (fun _ => peerGetMaybeZeroPrefix_erases _))

theorem pubkeyLookupPrefix_preserves_ambient (c : AmbientContracts I) (key : Key) :
    PrefixPreserves I LifetimeEvent.Safe (pubkeyLookupPrefix key) := by
  unfold pubkeyLookupPrefix
  apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel))
  intro d
  apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
  intro _
  exact AmbientContracts.drop (peerGetMaybeZeroPrefix_spec_ambient c (fun _ => True) _)

end Leanux.Proofs.WG.Lifetimes
