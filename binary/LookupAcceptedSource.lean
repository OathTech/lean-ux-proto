import LookupHelperPrepared

namespace Binary.MirrorHistory
open Leanux Leanux.WG

/-- Acceptance of erasure supplies an actual successful logged execution. -/
theorem Erases.accepted_logs {logged : Logged α} {original : M α}
    (erased : Erases logged original) (world final : World) (answer : α)
    (accepted : original.run world = .ok (answer, final)) (history : List Point) :
    ∃ points, (logged.run history).run world = .ok ((answer, points), final) := by
  have equation := (erased history world).trans accepted
  cases run : (logged.run history).run world with
  | error error => simp [run, erase] at equation
  | ok out =>
    obtain ⟨⟨value, points⟩, after⟩ := out
    simp only [run, erase, Except.ok.injEq, Prod.mk.injEq] at equation
    obtain ⟨rfl, rfl⟩ := equation
    exact ⟨points, rfl⟩

theorem bind_accepted {first : Logged α} {next : α → Logged β}
    {history points : List Point} {world final : World} {answer : β}
    (accepted : ((first >>= next).run history).run world = .ok ((answer, points), final)) :
    ∃ value middle intermediate,
      (first.run history).run world = .ok ((value, middle), intermediate) ∧
      ((next value).run middle).run intermediate = .ok ((answer, points), final) := by
  cases run : (first.run history).run world with
  | error error =>
    simp only [StateT.run_bind, run] at accepted
    change Except.error error = Except.ok ((answer, points), final) at accepted
    contradiction
  | ok out =>
    obtain ⟨⟨value, middle⟩, intermediate⟩ := out
    simp only [StateT.run_bind, run] at accepted
    exact ⟨value, middle, intermediate, rfl, accepted⟩

/-- Extract the actual callee execution from its logged CALL/RET wrapper. -/
theorem called_accepted {action : Logged α} {symbol : String}
    {history points : List Point} {world final : World} {answer : α}
    (accepted : ((called symbol action).run history).run world = .ok ((answer, points), final)) :
    ∃ middle,
      (action.run (history ++ [⟨.call symbol, world⟩])).run world = .ok ((answer, middle), final) := by
  obtain ⟨unit, h, w, marked, rest⟩ := bind_accepted accepted
  rw [mark_run] at marked
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Prod.mk.inj (Except.ok.inj marked.symm)
  obtain ⟨value, middle, intermediate, run, rest⟩ := bind_accepted rest
  have finalEq : ((value, middle ++ [⟨.returned symbol, intermediate⟩]), intermediate) =
      ((answer, points), final) := by
    change Except.ok ((value, middle ++ [⟨.returned symbol, intermediate⟩]), intermediate) =
      Except.ok ((answer, points), final) at rest
    exact Except.ok.inj rest
  obtain ⟨⟨rfl, _⟩, rfl⟩ := Prod.mk.inj finalEq
  exact ⟨middle, run⟩
end Binary.MirrorHistory

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase

/-- Selection is the source search's actual result, including wrong-kind
    termination on the first index match. -/
theorem search_selected (c : Config) (es : List IndexEntry)
    (history : List MirrorHistory.Point) (world : World) :
    (LookupSearch.result c.kinds c.query es history world).1.1.map (·.owner) = selected c es := by
  induction es generalizing history world with
  | nil => rfl
  | cons e es ih =>
    cases hit : (e.index == c.query) with
    | false =>
      rw [LookupSearch.result_miss _ _ _ _ _ _ hit]
      simpa [selected, List.find?, hit] using ih _ _
    | true =>
      rw [LookupSearch.result_hit _ _ _ _ _ _ hit]
      cases kind : c.kinds.contains e.kind <;> simp [LookupSearch.finish, selected, List.find?, hit, kind]

/-- The nullable word is read through its selected owner, never from an
    index-table cache. Missing owners remain explicit source failures. -/
theorem owner_peerWord_run (world : World) (device : Device) (owner : IndexOwner)
    (word : Option PeerId) (hasDevice : world.k.wg = some device)
    (value : OwnerWord.value device owner = some word) :
    owner.peerWord.run world = .ok (word, world) := by
  cases owner with
  | handshake id =>
    cases present : device.peers[id]? with
    | none => simp [OwnerWord.value, present] at value
    | some peer =>
      simp [OwnerWord.value, present] at value
      subst word
      simp [IndexOwner.peerWord, getPeer, getDev, getK, hasDevice, present]
      rfl
  | keypair id =>
    cases present : device.keypairs[id]? with
    | none => simp [OwnerWord.value, present] at value
    | some kp =>
      simp [OwnerWord.value, present] at value
      subst word
      simp [IndexOwner.peerWord, getKeypair, getDev, getK, hasDevice, present]
      rfl

/-- The concrete source continuation after the helper, retained for the
    owner-store and final-result composition. -/
def afterHelper (owner : IndexOwner) (peer : Option PeerId) :
    MirrorHistory.Logged (Option (IndexOwner × PeerId)) := do
  StateT.lift (owner.setPeerWord peer)
  if ← MirrorHistory.branchLogged .idxPeerAlive peer.isSome then
    let some pid := peer | StateT.lift (invariant "unreachable")
    return some (owner, pid)
  return none

/-- Accepted lookup execution fixes a successful helper run and its actual
    accepted continuation. It adds no liveness or count-bound premise. -/
theorem lookup_accepts_helper (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (returnAddress : UInt64) (s : MachineState) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress s world v)
    (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (answer : Option (IndexOwner × PeerId)) (final : World)
    (accepted : (indexLookup c.kinds c.query).run world = .ok (answer, final)) :
    ∃ helperAnswer helperFinal middle points,
      (peerGetMaybeZero c.focus.peer).run (helperWorld c world v) = .ok (helperAnswer, helperFinal) ∧
      ((MirrorHistory.called "wg_peer_get_maybe_zero" (MirrorHistory.peerGet c.focus.peer)).run
        (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).1.2).run
        (helperWorld c world v) = .ok ((helperAnswer, middle), helperFinal) ∧
      ((afterHelper owner helperAnswer).run middle).run helperFinal = .ok ((answer, points), final) := by
  obtain ⟨points, logged⟩ := (MirrorHistory.lookup_erases c.kinds c.query).accepted_logs world final answer accepted []
  rw [LookupSearch.lookup_split] at logged
  obtain ⟨bodyPoints, bodyRun⟩ := MirrorHistory.called_accepted logged
  obtain ⟨es, initialPoints, initialWorld, bucketRun, prefixRun⟩ := MirrorHistory.bind_accepted bodyRun
  obtain ⟨device, hasDevice⟩ : ∃ device, world.k.wg = some device := by
    cases hd : world.k.wg with
    | none => have h := entry.projected; simp [project, hd] at h
    | some device => exact ⟨device, rfl⟩
  have bucketEq : v.bucket = device.indexTable.filter (fun e => e.index % 8192 == c.query % 8192) := by
    have h := congrArg (fun view : Option View => view.map (·.bucket)) entry.projected
    simpa [project, hasDevice] using h.symm
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure,
    LookupMirror.bucket_run c.query world device hasDevice] at bucketRun
  change Except.ok ((device.indexTable.filter (fun e => e.index % 8192 == c.query % 8192),
    [sourceEntry world]), world) = Except.ok ((es, initialPoints), initialWorld) at bucketRun
  have eq := Except.ok.inj bucketRun
  rw [← bucketEq] at eq
  have esEq := congrArg (fun p => p.1.1) eq
  have pointsEq := congrArg (fun p => p.1.2) eq
  have worldEq := congrArg Prod.snd eq
  dsimp only at esEq pointsEq worldEq
  subst es initialPoints initialWorld
  obtain ⟨found, beforePoints, beforeWorld, searched, suffixRun⟩ := MirrorHistory.bind_accepted prefixRun
  rw [LookupSearch.prefix_run] at searched
  have eq := Except.ok.inj searched
  have foundEq := congrArg (fun p => p.1.1) eq
  have pointsEq := congrArg (fun p => p.1.2) eq
  have worldEq := congrArg Prod.snd eq
  dsimp only at foundEq pointsEq worldEq
  subst found beforePoints beforeWorld
  have selection := (search_selected c v.bucket [sourceEntry world] world).trans (entry.focus.1.trans focused)
  cases found : (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).1.1 with
  | none => simp [found] at selection
  | some chosen =>
    have ownerEq : chosen.owner = owner := by simpa [found] using selection
    have sourceDevice : (helperWorld c world v).k.wg = some device := by
      rw [helperWorld, LookupSearch.result_world]
      exact hasDevice
    have wordValue : OwnerWord.value device owner = some c.focus.peer := by
      have focusedWord : v.ownerWord = some c.focus.peer := by
        simpa only [EntryFocus, focused] using entry.focus.2
      have h := congrArg (fun view : Option View => view.bind (·.ownerWord)) entry.projected
      simpa [project, hasDevice, focused, focusedWord] using h
    have getter := owner_peerWord_run (helperWorld c world v) device owner c.focus.peer sourceDevice wordValue
    rw [found] at suffixRun
    change ((do
      let word ← StateT.lift chosen.owner.peerWord
      let peer ← MirrorHistory.called "wg_peer_get_maybe_zero" (MirrorHistory.peerGet word)
      afterHelper chosen.owner peer).run _).run _ = _ at suffixRun
    rw [ownerEq] at suffixRun
    obtain ⟨word, afterReadPoints, afterReadWorld, readRun, rest⟩ := MirrorHistory.bind_accepted suffixRun
    simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, getter] at readRun
    change Except.ok ((c.focus.peer, _), helperWorld c world v) =
      Except.ok ((word, afterReadPoints), afterReadWorld) at readRun
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Prod.mk.inj (Except.ok.inj readRun.symm)
    obtain ⟨peer, middle, helperFinal, helperRun, continuation⟩ := MirrorHistory.bind_accepted rest
    refine ⟨peer, helperFinal, middle, bodyPoints, ?_, helperRun, continuation⟩
    have erased := MirrorHistory.called_erases "wg_peer_get_maybe_zero" _ _ (MirrorHistory.peerGet_erases c.focus.peer)
    have h := erased (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).1.2 (helperWorld c world v)
    rw [helperRun] at h
    exact h.symm

#print axioms lookup_accepts_helper
#print axioms search_selected
#print axioms owner_peerWord_run
#print axioms MirrorHistory.Erases.accepted_logs
#print axioms MirrorHistory.bind_accepted
#print axioms MirrorHistory.called_accepted
end Binary.LookupRelation
