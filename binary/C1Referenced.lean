import C1Source

/-! Result C1, proposition `ReferencedHolds` (`C1Interfaces`): the invariant
survives the caller taking or dropping one reference on a registered peer
between calls. This module is the prover's root in `binary/lakefile.toml`;
the hand-over is `binary/Statements/C1/proof/OPEN.md`, section 1.

Three steps. (1) The mirror's `peerGetMaybeZero` returning the peer, and its
`peerPut` from a count above one, each leave the device as it was with that
one peer's `refcount` replaced, and leave the pending records and the armed
sites alone. (2) The peer's count word is the only byte range the
reconstruction reads that `CountMoved` lets change, and the reconstruction
reads it as the mirror's count, so the reconstruction of the new memory is
`mapCounts` of the old one (`reconstruct_mapCounts`), which is the target of
the mirror's new device (`target_mapCounts`); the structural check does not
read the counts (`heap_mapCounts`, `heap_frame`). (3) The count word is in a
peer, apart from the arena, so `Idle` survives by the contract's `frame`. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1

/-! ## The mirror's two count operations, taken alone -/

/-- An accepted `peerGetMaybeZero` that returns the peer: the device with
that peer's count raised by one; no record consumed, no site armed or
disarmed. -/
theorem referenced_take_run {g g' : WGWorld} {a a' : Ambient} {d : Device} {pid : PeerId}
    (device : g.dev = some d)
    (run : ((WG.peerGetMaybeZero (some pid)).run g).run a = .ok ((some pid,g'),a')) :
    ∃ p, d.peers.get? pid = some p ∧
      g' = {g with dev := some {d with peers := d.peers.insert pid {p with refcount := p.refcount+1}}} ∧
      a'.hidden = a.hidden ∧ a'.allocArmed = a.allocArmed := by
  unfold WG.peerGetMaybeZero at run
  cases present : d.peers[pid]? with
  | none =>
    simp [Except.pure, Except.bind, StateT.run, bind, StateT.bind, StateT.lift, pure, StateT.pure, get, getThe,
      MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      monadLift, MonadLift.monadLift, AmbientM.branch, branch, WG.getPeer, WG.getDev,
      WG.requireNotPending, device, invariant, present, AmbientM.invariant, throw, throwThe,
      MonadExceptOf.throw] at run
  | some p =>
    refine ⟨p,present,?_⟩
    by_cases zero : p.refcount = 0 <;> by_cases wraps : 2147483647 ≤ p.refcount <;>
    simp [Except.pure, Except.bind, StateT.run, bind, StateT.bind, StateT.lift, pure, StateT.pure, get, getThe,
      MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      monadLift, MonadLift.monadLift, AmbientM.branch, AmbientM.branchCmp, AmbientM.unsupported,
      refcountIncNotZero, branchCmp, branch, unsupported, WG.getPeer, WG.setPeer, WG.getDev,
      WG.modifyDev, WG.requireNotPending, device, present, zero, wraps, throw, throwThe,
      MonadExceptOf.throw] at run
    obtain ⟨rfl,rfl⟩ := run
    exact ⟨rfl,rfl,rfl⟩

/-- An accepted `peerPut` on a peer whose count is above one: the device with
that peer's count lowered by one (no release); no record consumed, no site
armed or disarmed. -/
theorem referenced_drop_run {g g' : WGWorld} {a a' : Ambient} {d : Device} {pid : PeerId} {p : Peer}
    (device : g.dev = some d) (present : d.peers.get? pid = some p) (above : 1 < p.refcount)
    (run : ((WG.peerPut (some pid)).run g).run a = .ok (((),g'),a')) :
    g' = {g with dev := some {d with peers := d.peers.insert pid {p with refcount := p.refcount-1}}} ∧
      a'.hidden = a.hidden ∧ a'.allocArmed = a.allocArmed := by
  have present' : d.peers[pid]? = some p := present
  have positive : 0 < p.refcount := by omega
  have notOne : ¬p.refcount = 1 := by omega
  have notZero : ¬p.refcount = 0 := by omega
  unfold WG.peerPut at run
  simp [Except.pure, Except.bind, StateT.run, bind, StateT.bind, StateT.lift, pure, StateT.pure, get, getThe,
    MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    monadLift, MonadLift.monadLift, AmbientM.branch, AmbientM.branchCmp, AmbientM.unsupported,
    refcountDecAndTest, branchCmp, branch, unsupported, WG.getPeer, WG.setPeer, WG.getDev,
    WG.modifyDev, WG.requireNotPending, device, present', positive, notOne, notZero, throw, throwThe,
    MonadExceptOf.throw] at run
  obtain ⟨rfl,rfl⟩ := run
  exact ⟨rfl,rfl,rfl⟩

/-! ## The invariant across one peer's count word -/

/-- The layout's address of a registered peer names it. -/
theorem referenced_named {peers : List (Nat×Nat)} {pid peer : Nat}
    (address : Trie.address peers (some pid) = .ok peer) : (pid,peer) ∈ peers := by
  simp only [Trie.address] at address
  cases found : peers.find? (·.1 == pid) with
  | none => rw [found] at address; cases address
  | some pair =>
    rw [found] at address
    have equal : pair.2 = peer := Except.ok.inj address
    have key : pair.1 = pid := by simpa using List.find?_some found
    have member := List.mem_of_find?_eq_some found
    rcases pair with ⟨id,a⟩
    cases equal
    cases key
    exact member

/-- `Related` across a memory change that replaces one registered peer's
four-byte count, when the mirror's device changes by that peer's `refcount`
alone and its pending records and armed sites are as before. -/
theorem related_count {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator}
    (contract : AllocatorContract fetch L A) {w w' : World} {m m' : Mem 64} {pid : PeerId}
    {before after : Nat} (related : Related L A w m) (moved : CountMoved L pid before after m m')
    (effect : ∀ d p, w.wg.dev = some d → d.peers.get? pid = some p → p.refcount = before →
      w'.wg.dev = some {d with peers := d.peers.insert pid {p with refcount := after}} ∧
      w'.ambient.hidden = w.ambient.hidden ∧ w'.ambient.allocArmed = w.ambient.allocArmed) :
    Related L A w' m' := by
  obtain ⟨names,stream,table,peers,asserted,armedBefore,hidden,sites,apart,arena,idle⟩ := related
  obtain ⟨d,device,corresponds,shape⟩ := assertAt_ok asserted
  obtain ⟨peer,address,readBefore,readAfter,same⟩ := moved
  have fields := Trie.reconstruct_fields corresponds.trie
  have named : (pid,peer) ∈ names.trie.peers := peers ▸ referenced_named address
  obtain ⟨p,present,countRead⟩ := named_peer_count corresponds.trie named "peer.refcount"
  have mirrorCount : p.refcount = before :=
    Except.ok.inj ((readNat_of_word countRead).symm.trans readBefore)
  obtain ⟨device',hiddenSame,armedSame⟩ := effect d p device present mirrorCount
  have offset : Root.nodeOffsets.peerRefcount = 1056 := rfl
  have size : Layouts.peerSize = 1520 := rfl
  -- the bytes that may differ: the count word, and anything outside the heap
  let writes : BitVec 64 → Prop := fun a =>
    InRange (.ofNat 64 (peer+Root.nodeOffsets.peerRefcount)) 4 a ∨ ¬L.Heap a
  have outside : EqualOutside writes m m' := by
    intro a notWritten
    have inHeap : L.Heap a := Classical.not_not.mp fun out => notWritten (.inr out)
    exact same a inHeap fun count => notWritten (.inl count)
  have heapReads := readSpans_heap table peers arena
  have countSpan : (peer+Root.nodeOffsets.peerRefcount,4) ∈
      Trie.countSpans names.trie Root.nodeOffsets := List.mem_map.mpr ⟨(pid,peer),named,rfl⟩
  have untouched : ∀ span ∈ metadataSpans names Root.nodeOffsets, ∀ a, span.contains a → ¬writes a := by
    intro span member a inside written
    rcases written with count | out
    · exact spansApart_sound (metadata_count_apart corresponds) member countSpan inside count
    · exact out (heapReads span (metadataSpans_subset names _ span member) a inside)
  have metadata := MetadataSame.of_frame names Root.nodeOffsets outside untouched
  -- the count reads: the moved peer's is the new count, every other peer's is unchanged
  have g := geometry corresponds
  have peerObjects : names.trie.peers.Pairwise fun x y =>
      disjointRanges x.2 Layouts.peerSize y.2 Layouts.peerSize = true :=
    List.pairwise_map.mp (List.pairwise_append.mp g.apart).2.1
  have counts : ∀ id a, (id,a) ∈ names.trie.peers →
      word m' "peer.refcount" (a+Root.nodeOffsets.peerRefcount) 4 =
        (word m "peer.refcount" (a+Root.nodeOffsets.peerRefcount) 4).map
          ((fun id old => if id=pid then after else old) id) := by
    intro id a member
    by_cases equal : id = pid
    · subst id
      have sameAddress : a = peer := congrArg Prod.snd (Option.some.inj
        ((Trie.find_identity fields.peerIds member).symm.trans (Trie.find_identity fields.peerIds named)))
      subst a
      have bound := (fields.peerRange pid peer named).2
      have mapped : ∃ v, word m' "peer.refcount" (peer+Root.nodeOffsets.peerRefcount) 4 = .ok v := by
        have fits : peer+Root.nodeOffsets.peerRefcount+4 ≤ 2^64 := by omega
        unfold word
        simp only [fits,↓reduceIte]
        cases bytes : m'.loadBytes (.ofNat 64 (peer+Root.nodeOffsets.peerRefcount)) 4 with
        | none =>
          simp only [readNat,bytes] at readAfter
          cases readAfter
        | some bs => exact ⟨_,rfl⟩
      obtain ⟨v,read⟩ := mapped
      have value : v = after := Except.ok.inj ((readNat_of_word read).symm.trans readAfter)
      rw [read,countRead,value]
      simp [Except.map]
    · have different : (id,a) ≠ (pid,peer) := fun same => equal (congrArg Prod.fst same)
      have objects := Trie.pairwise_mem_ne (R := fun x y : Nat×Nat =>
          disjointRanges x.2 Layouts.peerSize y.2 Layouts.peerSize = true)
        (fun x y h => by simpa only [disjointRanges,Bool.or_comm] using h)
        peerObjects member named different
      have boundA := (fields.peerRange id a member).2
      have boundPeer := (fields.peerRange pid peer named).2
      simp only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq] at objects
      have kept : ∀ x, InRange (.ofNat 64 (a+Root.nodeOffsets.peerRefcount)) 4 x → ¬writes x := by
        intro x inside written
        rcases written with count | out
        · have here := Span.location (span := (a+Root.nodeOffsets.peerRefcount,4)) (by simp only; omega) inside
          have there := Span.location (span := (peer+Root.nodeOffsets.peerRefcount,4)) (by simp only; omega) count
          simp only at here there
          omega
        · refine out (heapReads (a+Root.nodeOffsets.peerRefcount,4) ?_ x inside)
          exact List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.mpr
            ⟨(id,a),member,List.mem_map.mpr ⟨(Root.nodeOffsets.peerRefcount,4),by simp [peerFields],rfl⟩⟩))
      rw [← Trie.word_frame outside "peer.refcount" _ 4 kept]
      cases word m "peer.refcount" (a+Root.nodeOffsets.peerRefcount) 4 <;> simp [Except.map,equal]
  have corresponds' : Allowedips.Corresponds names Root.nodeOffsets m'
      {d with peers := d.peers.insert pid {p with refcount := after}} := by
    unfold Allowedips.Corresponds
    rw [reconstruct_mapCounts names Root.nodeOffsets m m' _ metadata counts,corresponds,
      target_mapCounts d pid after p present]
    rfl
  have shape' : heap names (target {d with peers := d.peers.insert pid {p with refcount := after}}) m' =
      .ok () := by
    rw [target_mapCounts d pid after p present,heap_mapCounts,
      ← heap_frame names Root.nodeOffsets (target d) outside untouched]
    exact shape
  refine ⟨names,stream,table,peers,assertAt_of_related device' corresponds' shape',?_,
    hiddenSame.trans hidden,sites,apart,arena,contract.frame m m' _ _ idle ?_⟩
  · unfold armed at armedBefore ⊢
    rw [armedSame]
    exact armedBefore
  · intro a inArena _
    obtain ⟨span,member,inside⟩ := inArena
    apply same a ⟨span,List.mem_append_right _ member,inside⟩
    intro count
    have countArena : spansApart (Trie.countSpans names.trie Root.nodeOffsets) L.arena = true :=
      spansApart_within apart (count_objects peers) (Within.of_subset fun _ member => member)
    exact spansApart_sound countArena countSpan member count inside

/-! ## `Referenced` for `Inv` -/

theorem referencedHolds : ReferencedHolds := by
  intro fetch L A premises w w' m m' pid count related step
  rcases step with ⟨run,moved⟩ | ⟨run,above,moved⟩
  · refine related_count premises.allocator related moved ?_
    intro d p device present equal
    obtain ⟨g',a',inner,rfl⟩ := run_liftWG_acc run
    obtain ⟨p',present',rfl,hiddenSame,armedSame⟩ := referenced_take_run device inner
    cases Option.some.inj (present'.symm.trans present)
    subst equal
    exact ⟨rfl,hiddenSame,armedSame⟩
  · refine related_count premises.allocator related moved ?_
    intro d p device present equal
    obtain ⟨g',a',inner,rfl⟩ := run_liftWG_acc run
    subst equal
    obtain ⟨rfl,hiddenSame,armedSame⟩ := referenced_drop_run device present above inner
    exact ⟨rfl,hiddenSame,armedSame⟩

#print axioms referencedHolds

end Binary.Statements.C1.Proof
