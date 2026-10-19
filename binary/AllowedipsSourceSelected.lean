import SourceAdapter
import AllowedipsSourceFrames

namespace Binary.AllowedipsSource
open Leanux Leanux.WG MirrorHistory LookupSourceFrame

def searchPrefix (root : Option NodeId) (bits key : Nat) : Logged (Option NodeId) := do
  AllowedipsSource.swapEndian bits
  let node ← findNode root bits key
  _ ← branchLogged .lookupFound node.isSome
  return node

def afterPeer (peer : Option PeerId) : Logged (Option PeerId) := do
  if ← branchLogged .lookupPeerGone peer.isNone then
    StateT.lift (unsupported "lookup retry after a dying peer")
  return peer

def searchSuffix (node : Option NodeId) : Logged (Option PeerId) := do
  match node with
  | none => return none
  | some id =>
    let n ← StateT.lift (Source.getNode id)
    let peer ← called "wg_peer_get_maybe_zero" (peerGet n.peer)
    afterPeer peer

theorem lookup_split (root : Option NodeId) (bits key : Nat) :
    lookup root bits key = called "lookup" (searchPrefix root bits key >>= searchSuffix) := by
  simp only [lookup, searchPrefix, searchSuffix, afterPeer, bind_assoc, pure_bind]
  congr 1
  congr 1
  funext ignored
  congr 1
  funext node
  cases node <;> rfl

theorem frames_searchPrefix (project : WGWorld → σ) (root : Option NodeId) (bits key : Nat) :
    Frames (fun w => project w.wg) (searchPrefix root bits key) := by
  unfold searchPrefix
  apply frames_bind (frames_swapEndian project bits)
  intro _
  apply frames_bind (frames_findNode project root bits key)
  intro node
  apply frames_bind (frames_branch_kernel project _ _)
  intro _
  exact frames_pure _ node

/-- Mask just the returned peer's refcount. Peer existence, other peers'
    counts, and every other WireGuard field remain observations. -/
def selectedSnapshot (selected : Option PeerId) (k : WGWorld) :
    Option Device × (PeerId → Option Peer) :=
  (k.dev.map fun d => {d with peers := {}},
   fun pid => (k.dev.bind fun d => d.peers.get? pid).map fun p =>
     if selected = some pid then {p with refcount := 0} else p)

theorem peerFinal_selected (pid : PeerId) (w : World) (device : Device) (peer : Peer)
    (hasDevice : w.wg.dev = some device) (hasPeer : device.peers.get? pid = some peer) :
    selectedSnapshot (if peer.refcount = 0 then none else some pid)
      (PeerMirror.peerFinal pid w peer).wg =
    selectedSnapshot (if peer.refcount = 0 then none else some pid) w.wg := by
  by_cases zero : peer.refcount = 0
  · simp [PeerMirror.peerFinal, PeerMirror.countRecords, PeerMirror.recordCmp,
      LookupMirror.record, zero]
  · simp only [PeerMirror.peerFinal, PeerMirror.countRecords, PeerMirror.recordCmp,
      LookupMirror.record, beq_iff_eq, zero, ↓reduceIte]
    apply Prod.ext
    · simp [selectedSnapshot, hasDevice]
    · funext other
      by_cases same : pid = other
      · subst other
        have found : device.peers[pid]? = some peer := hasPeer
        simp [selectedSnapshot, hasDevice, found]
      · simp [selectedSnapshot, hasDevice, Std.TreeMap.getElem?_insert, same]

/-- The selected identity is the actual helper result, so null and dead
    results preserve every count; a live result may change only its count. -/
theorem peerGet_selected (word : Option PeerId) (history points : List Point)
    (w final : World) (answer : Option PeerId)
    (accepted : ((peerGet word).run history).run w = .ok ((answer,points),final))
    (prior : ∀ p ∈ history, selectedSnapshot answer p.world.wg = selectedSnapshot answer w.wg) :
    selectedSnapshot answer final.wg = selectedSnapshot answer w.wg ∧
      ∀ p ∈ points, selectedSnapshot answer p.world.wg = selectedSnapshot answer w.wg := by
  cases word with
  | none =>
    rw [peer_null_run_logged] at accepted
    cases accepted
    refine ⟨rfl,?_⟩
    intro p member
    rcases List.mem_append.mp member with old | added
    · exact prior p old
    · have eq := List.mem_singleton.mp added
      subst p
      rfl
  | some pid =>
    have erased := peerGet_erases (some pid) history w
    rw [accepted] at erased
    have actual : (Source.peerGetMaybeZero (some pid)).run w = .ok (answer,final) := erased.symm
    cases hd : w.wg.dev with
    | none =>
      simp [Except.pure, Except.bind, StateT.run, liftWG, bind, StateT.bind, StateT.lift, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, WG.peerGetMaybeZero, WG.requireNotPending, WG.getPeer, WG.getDev, AmbientM.branch, monadLift, MonadLift.monadLift, liftAmbient, Source.peerGetMaybeZero, branch, Source.requireNotPending, Source.getPeer, Source.getDev, Source.getWG, hd, invariant] at actual
      cases actual
    | some device =>
      cases hp : device.peers.get? pid with
      | none =>
        have absent : device.peers[pid]? = none := hp
        simp [Except.pure, Except.bind, StateT.run, liftWG, bind, StateT.bind, StateT.lift, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, WG.peerGetMaybeZero, WG.requireNotPending, WG.getPeer, WG.getDev, AmbientM.branch, monadLift, MonadLift.monadLift, liftAmbient, Source.peerGetMaybeZero, branch, Source.requireNotPending, Source.getPeer, Source.getDev, Source.getWG, hd, absent,
          invariant] at actual
        cases actual
      | some peer =>
        have bound := PeerMirror.accepted_peer_bound pid w final answer device peer hd hp actual
        rw [peer_run_logged pid history w device peer hd hp bound] at accepted
        cases accepted
        refine ⟨peerFinal_selected pid w device peer hd hp,?_⟩
        intro p member
        rcases List.mem_append.mp member with old | added
        · exact prior p old
        · exact congrArg (selectedSnapshot _) (peerPoints_kernel w peer p added)

theorem called_accepted {action : Logged α} {symbol : String}
    {history points : List Point} {world final : World} {answer : α}
    (accepted : ((called symbol action).run history).run world = .ok ((answer,points),final)) :
    ∃ middle,
      (action.run (history ++ [⟨.call symbol,world⟩])).run world = .ok ((answer,middle),final) ∧
      points = middle ++ [⟨.returned symbol,final⟩] := by
  obtain ⟨ignored,h,w,marked,rest⟩ := accepted_bind _ _ _ _ _ accepted
  rw [mark_run] at marked
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := Prod.mk.inj (Except.ok.inj marked.symm)
  obtain ⟨value,middle,intermediate,run,rest⟩ := accepted_bind _ _ _ _ _ rest
  change Except.ok ((value,middle ++ [⟨.returned symbol,intermediate⟩]),intermediate) =
    Except.ok ((answer,points),final) at rest
  obtain ⟨⟨rfl,eq⟩,rfl⟩ := Prod.mk.inj (Except.ok.inj rest)
  exact ⟨middle,run,rfl⟩

theorem afterPeer_accepted (peer answer : Option PeerId) (history points : List Point)
    (w final : World)
    (accepted : ((afterPeer peer).run history).run w = .ok ((answer,points),final)) :
    peer = answer ∧ peer.isSome = true ∧
      final = LookupMirror.record w .lookupPeerGone false ∧
      points = history ++ [⟨.decision .lookupPeerGone,final⟩] := by
  cases peer with
  | none =>
    simp [afterPeer, branchLogged, mark, branch, unsupported] at accepted
    cases accepted
  | some pid =>
    change Except.ok ((some pid,history ++ [⟨.decision .lookupPeerGone,
      LookupMirror.record w .lookupPeerGone false⟩]), LookupMirror.record w .lookupPeerGone false) =
      Except.ok ((answer,points),final) at accepted
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := Prod.mk.inj (Except.ok.inj accepted)
    exact ⟨rfl,rfl,rfl,rfl⟩

#print axioms lookup_split
#print axioms peerGet_selected
#print axioms afterPeer_accepted

theorem searchSuffix_selected (node : Option NodeId) (history points : List Point)
    (w final : World) (answer : Option PeerId)
    (accepted : ((searchSuffix node).run history).run w = .ok ((answer,points),final))
    (prior : ∀ p ∈ history, selectedSnapshot answer p.world.wg = selectedSnapshot answer w.wg) :
    selectedSnapshot answer final.wg = selectedSnapshot answer w.wg ∧
      ∀ p ∈ points, selectedSnapshot answer p.world.wg = selectedSnapshot answer w.wg := by
  cases node with
  | none =>
    change Except.ok ((none,history),w) = Except.ok ((answer,points),final) at accepted
    cases accepted
    exact ⟨rfl,prior⟩
  | some id =>
    obtain ⟨n,readPoints,readWorld,read,rest⟩ := accepted_bind _ _ _ _ _ accepted
    obtain ⟨peer,helperPoints,helperWorld,helper,tail⟩ := accepted_bind _ _ _ _ _ rest
    obtain ⟨peerEq,live,finalEq,pointsEq⟩ := afterPeer_accepted peer answer _ _ _ _ tail
    subst peer
    have readFrames := frames_lift (preserves_getNode (fun w => selectedSnapshot answer w.wg) id)
      (selectedSnapshot answer w.wg) history w n readPoints readWorld rfl prior read
    obtain ⟨inner,innerRun,helperEq⟩ := called_accepted helper
    have priorHelper : ∀ p ∈ readPoints ++ [⟨.call "wg_peer_get_maybe_zero",readWorld⟩],
        selectedSnapshot answer p.world.wg = selectedSnapshot answer readWorld.wg := by
      intro p member
      rcases List.mem_append.mp member with old | callPoint
      · exact (readFrames.2 p old).trans readFrames.1.symm
      · have eq := List.mem_singleton.mp callPoint
        subst p
        rfl
    have helperFrames := peerGet_selected n.peer _ inner readWorld helperWorld answer innerRun priorHelper
    have finalKernel : final.wg = helperWorld.wg := by rw [finalEq]; rfl
    have finalFrame : selectedSnapshot answer final.wg = selectedSnapshot answer w.wg :=
      (congrArg (selectedSnapshot answer) finalKernel).trans (helperFrames.1.trans readFrames.1)
    refine ⟨finalFrame,?_⟩
    intro p member
    rw [pointsEq, helperEq] at member
    rcases List.mem_append.mp member with earlier | decision
    · rcases List.mem_append.mp earlier with innerPoint | returned
      · exact (helperFrames.2 p innerPoint).trans readFrames.1
      · have eq := List.mem_singleton.mp returned
        subst p
        exact helperFrames.1.trans readFrames.1
    · have eq := List.mem_singleton.mp decision
      subst p
      exact finalFrame

/-- Every actual logged point preserves all WireGuard state except the
    actual returned peer's reference count. A miss masks no count at all.
    The helper's increment remains after its dead=false decision and before
    its return point, as fixed by `peer_run_logged`. -/
theorem lookup_selected (root : Option NodeId) (bits key : Nat)
    (world final : World) (answer : Option PeerId) (points : List Point)
    (accepted : ((lookup root bits key).run []).run world = .ok ((answer,points),final)) :
    selectedSnapshot answer final.wg = selectedSnapshot answer world.wg ∧
      ∀ p ∈ points, selectedSnapshot answer p.world.wg = selectedSnapshot answer world.wg := by
  rw [lookup_split] at accepted
  obtain ⟨inner,innerRun,pointsEq⟩ := called_accepted accepted
  obtain ⟨node,searchPoints,searchWorld,search,rest⟩ := accepted_bind _ _ _ _ _ innerRun
  have searchFrames := frames_searchPrefix (selectedSnapshot answer) root bits key
    (selectedSnapshot answer world.wg) [⟨.call "lookup",world⟩] world node searchPoints searchWorld
    rfl (by intro p member; have eq := List.mem_singleton.mp member; subst p; rfl) search
  have prior : ∀ p ∈ searchPoints,
      selectedSnapshot answer p.world.wg = selectedSnapshot answer searchWorld.wg := by
    intro p member
    exact (searchFrames.2 p member).trans searchFrames.1.symm
  have suffixFrames := searchSuffix_selected node searchPoints inner searchWorld final answer rest prior
  have finalFrame := suffixFrames.1.trans searchFrames.1
  refine ⟨finalFrame,?_⟩
  intro p member
  rw [pointsEq] at member
  rcases List.mem_append.mp member with old | returned
  · exact (suffixFrames.2 p old).trans searchFrames.1
  · have eq := List.mem_singleton.mp returned
    subst p
    exact finalFrame

#print axioms lookup_selected
end Binary.AllowedipsSource
