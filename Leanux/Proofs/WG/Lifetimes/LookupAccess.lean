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
    ErasesStatePrefix (requireNotPendingMixed pid what) (requireNotPending pid what) :=
  erasesStatePrefix_pure _

theorem requireNotPendingMixed_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (what : String) :
    AmbientSpec I P (requireNotPendingMixed pid what) (fun _ => P) := c.pure P _

def peerGetMaybeZeroPrefix (peer : Option PeerId) : MixedM (Option PeerId) := do
  if ← liftWGPrefix (branch .peerGetMaybeZeroNull peer.isNone) then return none
  let some pid := peer | liftWGPrefix (invariant "unreachable")
  requireNotPendingMixed pid "a reference count the handshake worker also changes"
  let p ← getPeerMixed pid
  let live ← liftWGPrefix (refcountIncNotZero p.refcount)
  if ← liftWGPrefix (branch .peerGetMaybeZeroDead !live) then return none
  setPeerMixed pid {p with refcount := p.refcount + 1}
  return some pid

theorem peerGetMaybeZeroPrefix_erases (peer : Option PeerId) :
    ErasesStatePrefix (peerGetMaybeZeroPrefix peer) (peerGetMaybeZero peer) := by
  unfold peerGetMaybeZeroPrefix peerGetMaybeZero
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro isNull
  split
  · exact erasesStatePrefix_pure _
  · cases peer with
    | none => exact erasesStatePrefix_lift _
    | some pid =>
      apply erasesStatePrefix_bind (requireNotPendingMixed_erases pid _)
      intro _
      apply erasesStatePrefix_bind (getPeerMixed_erases pid)
      intro p
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro live
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro dead
      split
      · exact erasesStatePrefix_pure _
      · exact erasesStatePrefix_bind (setPeerMixed_erases pid _) (fun _ => erasesStatePrefix_pure _)

theorem peerGetMaybeZeroPrefix_spec_ambient (c : AmbientContracts I)
    (P : IdentityView → Prop) (peer : Option PeerId) :
    AmbientSpec I P (peerGetMaybeZeroPrefix peer) (fun _ => P) := by
  unfold peerGetMaybeZeroPrefix
  apply StatePrefixEnsures.bind (c.branch P _ _)
  intro isNull
  split
  · exact c.pure P _
  · cases peer with
    | none => exact c.invariant P _
    | some pid =>
      apply StatePrefixEnsures.bind (requireNotPendingMixed_spec c P pid _)
      intro _
      apply StatePrefixEnsures.bind (c.getPeer P pid)
      intro p
      let Q := fun s : IdentityView => P s ∧ s.1.slots pid = some p.internalId
      have href : AmbientSpec I Q (liftWGPrefix (refcountIncNotZero p.refcount)) (fun _ => Q) := by
        apply c.store
        intro initial
        have ambient (α : Type) (a : AmbientM α) :
            Hoare (MonadLift.monadLift a : WG.M α) (fun w => wgStoreView w = initial)
              (fun _ w => wgStoreView w = initial) :=
          hoare_liftAmbient a (fun w => wgStoreView w = initial)
        unfold Hoare at *
        mvcgen [-Std.Do.Spec.monadLift_StateT, refcountIncNotZero,
          branchCmp, branch, unsupported, ambient]
      apply StatePrefixEnsures.bind href
      intro live
      apply StatePrefixEnsures.bind (c.branch Q _ _)
      intro dead
      split
      · exact AmbientContracts.forget (c.pure Q none) (fun _ _ hi => hi.1)
      · apply StatePrefixEnsures.bind (c.setPeer P pid {p with refcount := p.refcount + 1})
        intro _
        exact c.pure P _

def indexLookupPrefix (kinds : List IndexKind) (index : Nat) : MixedM (Option (IndexOwner × PeerId)) := do
  let mut entry : Option IndexEntry := none
  let mut stopped := false
  for e in ← liftWGPrefix (liftIndex (indexBucket index)) do
    _ ← liftWGPrefix (branch .idxWalk true)
    if ← liftWGPrefix (branch .idxMatch (e.index == index)) then
      if ← liftWGPrefix (branch .idxTypeMatch (kinds.contains e.kind)) then entry := some e
      stopped := true
      break
  if !stopped then _ ← liftWGPrefix (branch .idxWalk false)
  if ← liftWGPrefix (branch .idxFound entry.isSome) then
    let some e := entry | liftWGPrefix (invariant "unreachable")
    let peer ← peerGetMaybeZeroPrefix (← peerWordPrefix e.owner)
    setPeerWordPrefix e.owner peer
    if ← liftWGPrefix (branch .idxPeerAlive peer.isSome) then
      let some pid := peer | liftWGPrefix (invariant "unreachable")
      return some (e.owner, pid)
  return none

theorem indexLookupPrefix_erases (kinds : List IndexKind) (index : Nat) :
    ErasesStatePrefix (indexLookupPrefix kinds index) (indexLookup kinds index) := by
  unfold indexLookupPrefix indexLookup
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro bucket
  apply erasesStatePrefix_bind
  · apply erasesStatePrefix_forIn
    intro e state
    rcases state with ⟨entry, stopped⟩
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro _
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro same
    split
    · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro kind
      split <;> exact erasesStatePrefix_pure _
    · exact erasesStatePrefix_pure _
  · intro state
    rcases state with ⟨entry, stopped⟩
    dsimp only
    have tail : ErasesStatePrefix
        (do if ← liftWGPrefix (branch .idxFound entry.isSome) then
              let some e := entry | liftWGPrefix (invariant "unreachable")
              let peer ← peerGetMaybeZeroPrefix (← peerWordPrefix e.owner)
              setPeerWordPrefix e.owner peer
              if ← liftWGPrefix (branch .idxPeerAlive peer.isSome) then
                let some pid := peer | liftWGPrefix (invariant "unreachable")
                return some (e.owner, pid)
            return none)
        (do if ← branch .idxFound entry.isSome then
              let some e := entry | invariant "unreachable"
              let peer ← peerGetMaybeZero (← e.owner.peerWord)
              e.owner.setPeerWord peer
              if ← branch .idxPeerAlive peer.isSome then
                let some pid := peer | invariant "unreachable"
                return some (e.owner, pid)
            return none) := by
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro found
      split
      · cases entry with
        | none => exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_pure _)
        | some e =>
          apply erasesStatePrefix_bind (peerWordPrefix_erases _)
          intro word
          apply erasesStatePrefix_bind (peerGetMaybeZeroPrefix_erases _)
          intro peer
          apply erasesStatePrefix_bind (setPeerWordPrefix_erases _ _)
          intro _
          apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
          intro alive
          split
          · cases peer <;> first | exact erasesStatePrefix_pure _ | exact erasesStatePrefix_lift _
          · exact erasesStatePrefix_pure _
      · exact erasesStatePrefix_pure _
    split
    · exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => tail)
    · exact tail

theorem indexBucket_sameStore (index : Nat) : SameWGStore (liftIndex (indexBucket index)) := by
  intro initial
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr
  rw [liftIndex_run] at hr
  cases hd : w.dev with
  | none => simp [hd] at hr
  | some d =>
    cases hb : ((indexBucket index).run d.indexTable).run ambient with
    | error e => simp [hd, hb, Except.map] at hr
    | ok out =>
      rcases out with ⟨⟨bucket, table⟩, nextAmbient⟩
      have ht : table = d.indexTable :=
        (ProjectedAction.iff_run_ambient _ _ _).mp (Framing.indexBucket_sameTable index)
          d.indexTable ambient bucket table nextAmbient hb
      subst table
      simp only [hd, hb, Except.map, Except.ok.injEq, Prod.mk.injEq] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      simpa only [← hd] using hi

theorem indexLookupPrefix_preserves_ambient (c : AmbientContracts I)
    (kinds : List IndexKind) (index : Nat) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (indexLookupPrefix kinds index) := by
  unfold indexLookupPrefix
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _ (indexBucket_sameStore index)))
  intro bucket
  apply StatePrefixEnsures.bind
  · apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) LifetimeEvent.Safe
      (fun _ h w _ hi => c.safe h w hi)
    intro e state
    rcases state with ⟨entry, stopped⟩
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro _
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro same
    split
    · apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro kind
      split <;> exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
  · intro state
    rcases state with ⟨entry, stopped⟩
    dsimp only
    have tail : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
        (do if ← liftWGPrefix (branch .idxFound entry.isSome) then
              let some e := entry | liftWGPrefix (invariant "unreachable")
              let peer ← peerGetMaybeZeroPrefix (← peerWordPrefix e.owner)
              setPeerWordPrefix e.owner peer
              if ← liftWGPrefix (branch .idxPeerAlive peer.isSome) then
                let some pid := peer | liftWGPrefix (invariant "unreachable")
                return some (e.owner, pid)
            return none) := by
      apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro found
      split
      · cases entry with
        | none =>
          apply StatePrefixEnsures.bind (AmbientContracts.drop (c.invariant (fun _ => True) _))
          intro _
          exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
        | some e =>
          apply StatePrefixEnsures.bind (AmbientContracts.drop (peerWordPrefix_spec c (fun _ => True) _))
          intro word
          apply StatePrefixEnsures.bind (AmbientContracts.drop (peerGetMaybeZeroPrefix_spec_ambient c (fun _ => True) _))
          intro peer
          apply StatePrefixEnsures.bind (AmbientContracts.drop (setPeerWordPrefix_spec c (fun _ => True) _ _))
          intro _
          apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
          intro alive
          split
          · cases peer
            · exact AmbientContracts.drop (c.invariant (fun _ => True) _)
            · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
          · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
      · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    split
    · exact StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _)) (fun _ => tail)
    · exact tail

def pubkeyLookupPrefix (key : Key) : MixedM (Option PeerId) := do
  let found := ((← liftWGPrefix getDev).peerHashtable.find? (·.1 == key)).map (·.2)
  _ ← liftWGPrefix (branch .pubkeyLookupMatch found.isSome)
  peerGetMaybeZeroPrefix found

theorem pubkeyLookupPrefix_erases (key : Key) :
    ErasesStatePrefix (pubkeyLookupPrefix key) (pubkeyLookup key) := by
  unfold pubkeyLookupPrefix pubkeyLookup
  exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
    erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => peerGetMaybeZeroPrefix_erases _))

theorem pubkeyLookupPrefix_preserves_ambient (c : AmbientContracts I) (key : Key) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (pubkeyLookupPrefix key) := by
  unfold pubkeyLookupPrefix
  have hd : SameWGStore getDev := by
    intro initial
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient d v ambient' hi hr
    cases hw : w.dev with
    | none =>
      simp [getDev, hw, invariant, AmbientM.invariant] at hr
      cases hr
    | some dev =>
      simp [getDev, hw] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact hi
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _ hd))
  intro d
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
  intro _
  exact AmbientContracts.drop (peerGetMaybeZeroPrefix_spec_ambient c (fun _ => True) _)

/-- Product callers keep arbitrary invariants of their actual World. -/
theorem requireNotPendingMixed_spec_product (c : ProductAmbientContracts I)
    (P : IdentityView → Prop) (pid : PeerId) (what : String) :
    ProductAmbientSpec I P (liftWGObserver (requireNotPendingMixed pid what)) (fun _ => P) := by
  simpa only [requireNotPendingMixed, liftWGObserver_pure] using c.pure P ()

theorem peerGetMaybeZeroPrefix_spec_product (c : ProductAmbientContracts I)
    (P : IdentityView → Prop) (peer : Option PeerId) :
    ProductAmbientSpec I P (liftWGObserver (peerGetMaybeZeroPrefix peer)) (fun _ => P) := by
  have branch_spec (Q : IdentityView → Prop) (d : Decision) (b : Bool) :
      ProductAmbientSpec I Q (liftWGObserver (liftWGPrefix (Leanux.branch d b))) (fun _ => Q) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  simp only [peerGetMaybeZeroPrefix, liftWGObserver_bind]
  apply PrefixEnsures.bind (branch_spec P _ _)
  intro isNull
  split
  · simpa only [liftWGObserver_pure] using c.pure P none
  · cases peer with
    | none =>
      apply c.nativeStore
      intro initial
      exact hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial)
    | some pid =>
      simp only [liftWGObserver_bind]
      apply PrefixEnsures.bind (requireNotPendingMixed_spec_product c P pid _)
      intro _
      apply PrefixEnsures.bind (c.getPeer P pid)
      intro p
      let Q := fun s : IdentityView => P s ∧ s.1.slots pid = some p.internalId
      have href : ProductAmbientSpec I Q
          (liftWGObserver (liftWGPrefix (refcountIncNotZero p.refcount))) (fun _ => Q) := by
        apply c.nativeStore
        intro initial
        have ambient (α : Type) (a : AmbientM α) :
            Hoare (MonadLift.monadLift a : WG.M α) (fun w => wgStoreView w = initial)
              (fun _ w => wgStoreView w = initial) :=
          hoare_liftAmbient a (fun w => wgStoreView w = initial)
        unfold Hoare at *
        mvcgen [-Std.Do.Spec.monadLift_StateT, refcountIncNotZero,
          branchCmp, branch, unsupported, ambient]
      apply PrefixEnsures.bind href
      intro live
      apply PrefixEnsures.bind (branch_spec Q _ _)
      intro dead
      split
      · simpa only [liftWGObserver_pure] using
          ProductAmbientContracts.forget (c.pure Q none) (fun _ _ hi => hi.1)
      · simp only [liftWGObserver_bind, liftWGObserver_pure]
        apply PrefixEnsures.bind (c.setPeer P pid {p with refcount := p.refcount + 1})
        intro _
        exact c.pure P _

private theorem lookup_lift_forIn (xs : List α) (init : β)
    (f : α → β → MixedM (ForInStep β)) :
    liftWGObserver (forIn xs init f) =
      forIn xs init (fun x b => liftWGObserver (f x b)) := by
  induction xs generalizing init with
  | nil => simp only [List.forIn_nil, liftWGObserver_pure]
  | cons x xs ih =>
    simp only [List.forIn_cons, liftWGObserver_bind]
    congr 1
    funext step
    cases step with
    | done b => exact liftWGObserver_pure b
    | yield b => exact ih b

theorem indexLookupPrefix_preserves_product (c : ProductAmbientContracts I)
    (kinds : List IndexKind) (index : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (indexLookupPrefix kinds index)) := by
  have branch_spec (d : Decision) (b : Bool) :
      ProductAmbientSpec I (fun _ => True) (liftWGObserver (liftWGPrefix (Leanux.branch d b)))
        (fun _ _ => True) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  have invariant_spec (α : Type) :
      ProductAmbientSpec I (fun _ => True)
        (liftWGObserver (liftWGPrefix (Leanux.invariant (α := α) "unreachable")))
        (fun _ _ => True) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial)
  have word (owner : IndexOwner) : ProductAmbientSpec I (fun _ => True)
      (liftWGObserver (peerWordPrefix owner)) (fun _ _ => True) := by
    cases owner with
    | handshake pid =>
      simp only [peerWordPrefix, liftWGObserver_bind, liftWGObserver_pure]
      apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
      intro p
      exact ProductAmbientContracts.forget
        (c.pure (fun s => True ∧ s.1.slots pid = some p.internalId) p.handshakeEntryPeer)
        (fun _ _ hi => hi.1)
    | keypair kp =>
      simp only [peerWordPrefix, liftWGObserver_bind, liftWGObserver_pure]
      apply PrefixEnsures.bind (c.getKeypair (fun _ => True) kp)
      intro k
      exact ProductAmbientContracts.forget
        (c.pure (fun s => True ∧ s.2.1 kp = some k.internalId) k.peer)
        (fun _ _ hi => hi.1)
  have write (owner : IndexOwner) (peer : Option PeerId) : ProductAmbientSpec I (fun _ => True)
      (liftWGObserver (setPeerWordPrefix owner peer)) (fun _ _ => True) := by
    cases owner with
    | handshake pid =>
      simp only [setPeerWordPrefix, liftWGObserver_bind]
      apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
      intro p
      exact c.setPeer (fun _ => True) pid {p with handshakeEntryPeer := peer}
    | keypair kp =>
      simp only [setPeerWordPrefix, liftWGObserver_bind]
      apply PrefixEnsures.bind (c.getKeypair (fun _ => True) kp)
      intro k
      exact c.setKeypair (fun _ => True) kp {k with peer}
  simp only [indexLookupPrefix, liftWGObserver_bind, lookup_lift_forIn]
  apply PrefixPreserves.bind (ProductAmbientContracts.drop
    (c.nativeStore (fun _ => True) _ (indexBucket_sameStore index)))
  intro bucket
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn (hs := c.safe)
    intro e state
    rcases state with ⟨entry, stopped⟩
    simp only []
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec _ _))
    intro _
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec _ _))
    intro same
    split
    · simp only [liftWGObserver_bind]
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec _ _))
      intro kind
      split <;> simpa only [liftWGObserver_pure] using PrefixPreserves.pure c.safe _
    · simpa only [liftWGObserver_pure] using PrefixPreserves.pure c.safe _
  · intro state
    rcases state with ⟨entry, stopped⟩
    dsimp only
    have tail : PrefixPreserves I LifetimeEvent.Safe
        (liftWGObserver (do
          if ← liftWGPrefix (branch .idxFound entry.isSome) then
            let some e := entry | liftWGPrefix (invariant "unreachable")
            let peer ← peerGetMaybeZeroPrefix (← peerWordPrefix e.owner)
            setPeerWordPrefix e.owner peer
            if ← liftWGPrefix (branch .idxPeerAlive peer.isSome) then
              let some pid := peer | liftWGPrefix (invariant "unreachable")
              return some (e.owner, pid)
          return none)) := by
      simp only [liftWGObserver_bind]
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec _ _))
      intro found
      split
      · cases entry with
        | none =>
          simp only [liftWGObserver_bind, liftWGObserver_pure]
          apply PrefixPreserves.bind (ProductAmbientContracts.drop (invariant_spec _))
          intro _
          exact PrefixPreserves.pure c.safe _
        | some e =>
          simp only [liftWGObserver_bind]
          apply PrefixPreserves.bind (ProductAmbientContracts.drop (word _))
          intro peerWord
          apply PrefixPreserves.bind (ProductAmbientContracts.drop
            (peerGetMaybeZeroPrefix_spec_product c (fun _ => True) _))
          intro peer
          apply PrefixPreserves.bind (ProductAmbientContracts.drop (write _ _))
          intro _
          apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec _ _))
          intro alive
          split
          · cases peer with
            | none => exact ProductAmbientContracts.drop (invariant_spec _)
            | some pid => simpa only [liftWGObserver_pure] using PrefixPreserves.pure c.safe _
          · simpa only [liftWGObserver_pure] using PrefixPreserves.pure c.safe _
      · simpa only [liftWGObserver_pure] using PrefixPreserves.pure c.safe _
    split
    · simp only [liftWGObserver_bind]
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec _ _))
      intro _
      simpa only [liftWGObserver_bind] using tail
    · simpa only [liftWGObserver_bind] using tail

theorem pubkeyLookupPrefix_preserves_product (c : ProductAmbientContracts I) (key : Key) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (pubkeyLookupPrefix key)) := by
  have hd : SameWGStore getDev := by
    intro initial
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient d v ambient' hi hr
    cases hw : w.dev with
    | none =>
      simp [getDev, hw, invariant, AmbientM.invariant] at hr
      cases hr
    | some dev =>
      simp [getDev, hw] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact hi
  have branch_spec (d : Decision) (b : Bool) :
      ProductAmbientSpec I (fun _ => True) (liftWGObserver (liftWGPrefix (Leanux.branch d b)))
        (fun _ _ => True) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  simp only [pubkeyLookupPrefix, liftWGObserver_bind]
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ hd))
  intro d
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec _ _))
  intro _
  exact ProductAmbientContracts.drop (peerGetMaybeZeroPrefix_spec_product c (fun _ => True) _)

end Leanux.Proofs.WG.Lifetimes
