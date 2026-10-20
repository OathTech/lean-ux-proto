import SourceAdapter
import LookupHelperPhase
import PeerDecisionWorlds

namespace Binary.LookupRelation
open Leanux Leanux.WG LookupObservation PeerCountPhase

/-- The incoming source count is fixed by R and the actual loaded word,
    rather than an independently chosen ghost operand. -/
theorem R.focused_count (c : Config) (raw : List MachineState) (seen : List Point)
    (s : MachineState) (world : World) (related : R c raw seen s world)
    (pid : PeerId) (focused : c.focus.peer = some pid)
    (initial : scan none raw = none) (old : BitVec 32)
    (field : s.data.dmem.loadInt (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 = some (old.toNat : Int))
    (v : View) (projected : project c world = some v) (number : Nat)
    (count : v.count = some number) : number = old.toNat := by
  obtain ⟨_, ⟨actual, actualProjection, physical⟩, _⟩ := related
  have same : actual = v := Option.some.inj (actualProjection.symm.trans projected)
  subst actual
  have represented := physical.2.2.2
  simp only [focused] at represented
  obtain ⟨n, value, _, loaded⟩ := represented
  have numberEq : n = number := Option.some.inj (value.symm.trans count)
  subst n
  have noPhase : countPhase raw seen = none := by
    simp only [countPhase, initial, ite_self]
  simp only [noPhase, At] at loaded
  have sameCount := Option.some.inj (loaded.symm.trans field)
  omega

/-- Ordinary incoming count word, extracted from R without a fresh operand. -/
theorem R.initial_count (c : Config) (raw : List MachineState) (seen : List Point)
    (s : MachineState) (world : World) (related : R c raw seen s world)
    (initial : scan none raw = none) (v : View) (projected : project c world = some v)
    (pid : PeerId) (focused : c.focus.peer = some pid) (number : Nat) (count : v.count = some number) :
    PeerCountPhase.At none s.data.dmem (c.peers pid + BitVec.ofNat 64 Layouts.peer_refcount) number := by
  obtain ⟨actual, actualProjection, physical⟩ := related.2.1
  have same : actual = v := Option.some.inj (actualProjection.symm.trans projected)
  subst actual
  have represented := physical.2.2.2
  simp only [focused] at represented
  obtain ⟨n, value, _, loaded⟩ := represented
  have numberEq : n = number := Option.some.inj (value.symm.trans count)
  subst n
  have noPhase : countPhase raw seen = none := by simp only [countPhase, initial, ite_self]
  simpa only [noPhase] using loaded

/-- The count clause of R at each interior live-helper cut, derived from
    entry R, its actual load and the phase-aligned execution frames. -/
theorem helper_live_count_related (c : Config) (world : World) (s : MachineState)
    (history middle tail : List MachineState) (seen : List Point)
    (related : R c history seen s world) (pid : PeerId) (focused : c.focus.peer = some pid)
    (old : BitVec 32)
    (phase : IncrementingReturnAt history (history ++ middle) (history ++ middle ++ tail)
      (c.peers pid + .ofNat 64 Layouts.peer_refcount) old)
    (initial : scan none history = none)
    (field : s.data.dmem.loadInt (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 = some (old.toNat : Int))
    (writes : Address → Prop)
    (apart : ∀ j < 4, ¬writes (c.peers pid + .ofNat 64 Layouts.peer_refcount + .ofNat 64 j))
    (bound : old.toNat+1 < 2^32)
    (oldFrames : ∀ q ∈ middle, q.pc ∈ Image.cutPoints → EqualOutside writes s.data.dmem q.data.dmem)
    (newFrames : ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
      EqualOutside writes (s.data.dmem.storeInt (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 (old+1).toInt) q.data.dmem)
    (i : Nat) (current : MachineState)
    (present : (history ++ middle ++ tail)[i]? = some current)
    (later : history.length ≤ i) (proper : i+1 < (history ++ middle ++ tail).length)
    (cut : current.pc ∈ Image.cutPoints) (events : List Point) (active : helperActive events = true)
    (v : View) (projected : project c world = some v) (other : PeerId) (number : Nat)
    (focusOther : c.focus.peer = some other) (count : v.count = some number) :
    At (countPhase ((history ++ middle ++ tail).take (i+1)) events) current.data.dmem
      (c.peers other + .ofNat 64 Layouts.peer_refcount) number := by
  have idEq : other = pid := Option.some.inj (focusOther.symm.trans focused)
  subst other
  have numberEq := related.focused_count c history seen s world pid focused initial old field v projected number count
  rw [numberEq]
  exact helper_live_count_interior history middle tail _ old phase initial s.data.dmem writes
    field apart bound oldFrames newFrames i current present later proper cut events active

/-- Commit the live source count at the actual helper return into lookup.
    The only changed physical WG field is the focused count; embedded
    owner words, including a handshake in that same peer, are preserved. -/
theorem live_return_related (c : Config) (world : World) (device : Device)
    (pid : PeerId) (peer : Peer) (s current : MachineState)
    (history finalHistory : List MachineState) (seen : List Point)
    (nullPoint zeroPoint retry negative wrap dead : MachineState)
    (related : R c history seen s world)
    (hasDevice : world.wg.dev = some device) (hasPeer : device.peers.get? pid = some peer)
    (focused : c.focus.peer = some pid) (nonzero : peer.refcount ≠ 0)
    (noReturn : lastHelperReturn seen = none)
    (last : finalHistory.getLast? = some current)
    (pc : current.pc = Image.Lookup.entry+0xba)
    (writes : Address → Prop) (framed : EqualOutside writes s.data.dmem current.data.dmem)
    (bucketApart : ∀ v, project c world = some v → ∀ a, TrustBase.LookupBucketBytes c v a → ¬writes a)
    (ownerApart : ∀ a, TrustBase.LookupOwnerBytes c a → ¬writes a)
    (finalCount : current.data.dmem.loadInt (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 =
      some (peer.refcount+1 : Int)) :
    R c finalHistory
      ((seen ++ peerDecisions c.rxSection peer.refcount nullPoint zeroPoint retry negative wrap dead) ++
        [returned "wg_peer_get_maybe_zero" current]) current (PeerMirror.peerFinal pid world peer) := by
  obtain ⟨_, ⟨v, projected, physical⟩, steps⟩ := related
  let delta := peerDecisions c.rxSection peer.refcount nullPoint zeroPoint retry negative wrap dead
  have finalProjection := project_peerFinal c world device pid peer v hasDevice hasPeer focused projected
  rw [ite_eq_right nonzero] at finalProjection
  refine ⟨last, ⟨{v with count := some (peer.refcount+1)}, finalProjection, ?_⟩, ?_⟩
  · refine physical.frame_count_updated c history finalHistory seen _ s current v pid focused (peer.refcount+1)
      (ownerPending_none _ _ noReturn) ?_ writes framed (bucketApart v projected) ownerApart ?_
    · simp [ownerPending, pc, Image.Lookup.entry]
    · rw [countPhase_inactive _ _ (helperActive_return _ _)]
      exact finalCount
  · have advanced := steps.advance c seen delta world
    have log := peer_final_log world peer pid nullPoint zeroPoint retry negative wrap dead
    rw [steps.2] at log
    constructor
    · rw [log.1]
      simpa only [List.filterMap_append, List.filterMap_cons, returned, List.filterMap_nil,
        List.append_nil] using advanced.1
    · exact log.2

/-- A dead or NULL helper commits only its decision log. The ordinary
    count/owner equations are recovered from the actual unchanged bytes. -/
theorem unchanged_return_related (c : Config) (world world' : World) (s current : MachineState)
    (history finalHistory : List MachineState) (seen delta : List Point)
    (related : R c history seen s world)
    (sameProjection : project c world' = project c world)
    (sameSteps : world'.steps = (LookupSearch.advance world (delta.filterMap (·.step))).steps)
    (sameRx : world'.netRxSection = world.netRxSection)
    (initial : scan none history = none) (noReturn : lastHelperReturn seen = none)
    (last : finalHistory.getLast? = some current) (pc : current.pc = Image.Lookup.entry+0xba)
    (writes : Address → Prop) (framed : EqualOutside writes s.data.dmem current.data.dmem)
    (apart : ∀ v, project c world = some v → ∀ a, Reads c v a → ¬writes a) :
    R c finalHistory ((seen ++ delta) ++ [returned "wg_peer_get_maybe_zero" current]) current world' := by
  obtain ⟨_, ⟨v, projected, physical⟩, steps⟩ := related
  refine ⟨last, ⟨v, sameProjection.trans projected, ?_⟩, ?_⟩
  · refine physical.frame_count c history finalHistory seen _ s current v
      (ownerPending_none _ _ noReturn) (by simp [ownerPending, pc, Image.Lookup.entry])
      writes framed ?_ ?_ ?_
    · intro a read
      apply apart v projected a
      rcases read with head | node
      · exact .inl head
      · exact .inr (.inl node)
    · intro a read
      exact apart v projected a (.inr (.inr (.inl read)))
    · intro pid count focused countValue
      have represented := physical.2.2.2
      simp only [focused] at represented
      obtain ⟨number, value, _, loaded⟩ := represented
      have equal : number = count := Option.some.inj (value.symm.trans countValue)
      subst number
      have noPhase : countPhase history seen = none := by simp only [countPhase, initial, ite_self]
      rw [noPhase] at loaded
      rw [countPhase_inactive _ _ (helperActive_return _ _)]
      exact At.frame framed (fun j hj => apart v projected _ (.inr (.inr (.inr ⟨pid, focused, j, hj, rfl⟩)))) loaded
  · have advanced := steps.advance c seen delta world
    constructor
    · rw [sameSteps]
      simpa only [List.filterMap_append, List.filterMap_cons, returned, List.filterMap_nil,
        List.append_nil] using advanced.1
    · exact sameRx.trans steps.2

#print axioms R.initial_count
#print axioms unchanged_return_related
#print axioms live_return_related
#print axioms R.focused_count
#print axioms helper_live_count_related
end Binary.LookupRelation
