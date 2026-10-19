import SourceAdapter
import AllowedipsSource
import LookupSourceFrame

namespace Binary.AllowedipsSource
open Leanux Leanux.WG MirrorHistory LookupSourceFrame

theorem frames_branch_kernel (project : WGWorld → σ) (d : Decision) (b : Bool) :
    Frames (fun w => project w.wg) (branchLogged d b) := by
  unfold branchLogged
  apply frames_bind (frames_lift (show Preserves (fun w => project w.wg) (branch d b) from by
    intro w x w' run
    cases run
    rfl))
  intro answer
  apply frames_bind (frames_mark _ _)
  intro _
  exact frames_pure _ answer

theorem preserves_getNode (project : World → σ) (id : NodeId) :
    Preserves project (Source.getNode id) := by
  rw [Source.getNode_eq]
  apply preserves_bind (preserves_getDev project)
  intro d
  cases d.nodes.get? id with
  | none => exact preserves_throw project _
  | some n => exact preserves_pure project n

theorem preserves_choose (project : World → σ) (n : AipNode) (key : Nat) :
    Preserves project (choose n key) := by
  unfold choose
  split
  · apply preserves_bind (preserves_throw project _)
    intro _
    exact preserves_pure project _
  · exact preserves_pure project _

theorem preserves_bitAt (project : World → σ) (n : AipNode) (bit : Nat) :
    Preserves project (n.bitAt bit) := by
  unfold AipNode.bitAt
  split
  · exact preserves_pure project _
  · exact preserves_throw project _

theorem frames_commonBits (project : WGWorld → σ) (node : AipNode) (key bits : Nat) :
    Frames (fun w => project w.wg) (commonBits node key bits) := by
  intro initial history w answer points final same prior run
  rw [commonBits_run] at run
  cases run
  refine ⟨?_,?_⟩
  · have eq := congrArg World.wg (records_world w (commonChoices node key bits))
    exact (congrArg project eq).trans same
  · intro p member
    rcases List.mem_append.mp member with old | added
    · exact prior p old
    · have eq := congrArg World.wg (choicePoints_world w _ p added)
      exact (congrArg project eq).trans same

theorem frames_swapEndian (project : WGWorld → σ) (bits : Nat) :
    Frames (fun w => project w.wg) (AllowedipsSource.swapEndian bits) := by
  intro initial history w answer points final same prior run
  rw [swapEndian_run] at run
  cases run
  refine ⟨?_,?_⟩
  · have eq := congrArg World.wg (records_world w (swapChoices bits))
    exact (congrArg project eq).trans same
  · intro p member
    rcases List.mem_append.mp member with old | added
    · exact prior p old
    · have eq := congrArg World.wg (choicePoints_world w _ p added)
      exact (congrArg project eq).trans same

theorem frames_prefixMatches (project : WGWorld → σ) (node : AipNode) (key bits : Nat) :
    Frames (fun w => project w.wg) (prefixMatches node key bits) := by
  unfold prefixMatches
  apply frames_bind (frames_called _ (frames_commonBits project node key bits))
  intro common
  exact frames_pure _ _

theorem frames_iteration (project : WGWorld → σ) (bits key : Nat) (acc : Acc) :
    Frames (fun w => project w.wg) (iteration bits key acc) := by
  unfold iteration
  cases acc.2.1 with
  | none =>
    apply frames_bind (frames_branch_kernel project _ _)
    intro _
    exact frames_pure _ _
  | some id =>
    apply frames_bind (frames_branch_kernel project _ _)
    intro _
    apply frames_bind (frames_lift (preserves_getNode _ id))
    intro n
    apply frames_bind (frames_prefixMatches project n key bits)
    intro matching
    apply frames_bind (frames_branch_kernel project _ _)
    intro matching
    cases matching with
    | false => exact frames_pure _ _
    | true =>
      apply frames_bind (frames_branch_kernel project _ _)
      intro hasPeer
      cases hasPeer <;> apply frames_bind (frames_branch_kernel project _ _) <;> intro full
      all_goals cases full with
      | true => exact frames_pure _ _
      | false =>
        apply frames_bind (frames_lift (preserves_choose _ n key))
        intro bit
        apply frames_bind (frames_lift (preserves_bitAt _ n bit))
        intro next
        exact frames_pure _ _

theorem frames_loop (project : WGWorld → σ) (bits key fuel : Nat) (acc : Acc) :
    Frames (fun w => project w.wg) (loop bits key fuel acc) := by
  induction fuel generalizing acc with
  | zero => exact frames_pure _ acc
  | succ fuel ih =>
    unfold loop
    apply frames_bind (frames_iteration project bits key acc)
    intro step
    cases step with
    | done answer => exact frames_pure _ answer
    | yield next => exact ih next

theorem frames_findNode (project : WGWorld → σ) (trie : Option NodeId) (bits key : Nat) :
    Frames (fun w => project w.wg) (findNode trie bits key) := by
  rw [findNode_bounded]
  apply frames_bind (frames_loop project bits key 130 _)
  intro acc
  unfold finish
  cases acc.1 with
  | none => exact frames_lift (preserves_throw _ _)
  | some answer => exact frames_pure _ answer

/-- Before peer acquisition, every actual point and the final state retain
    the complete source Kernel. No trie or peer well-formedness assumption
    is needed: missing nodes and an exhausted loop fail in the mirror. -/
theorem findNode_kernel (trie : Option NodeId) (bits key : Nat)
    (world final : World) (answer : Option NodeId) (points : List Point)
    (accepted : ((findNode trie bits key).run []).run world = .ok ((answer,points),final)) :
    final.wg = world.wg ∧ ∀ p ∈ points, p.world.wg = world.wg :=
  frames_findNode id trie bits key world.wg [] world answer points final rfl
    (by intro p member; cases member) accepted

/-- Source-only frame observation: all WG device fields except the peer
    map, plus each peer's existence and all of its fields except refcount.
    This is a frame theorem, not a physical representation prerequisite. -/
def untouched (k : WGWorld) : Option Device × (PeerId → Option Peer) :=
  (k.dev.map fun d => {d with peers := {}},
   fun pid => (k.dev.bind fun d => d.peers.get? pid).map fun p => {p with refcount := 0})

theorem peerFinal_untouched (pid : PeerId) (w : World) (device : Device) (peer : Peer)
    (hasDevice : w.wg.dev = some device) (hasPeer : device.peers.get? pid = some peer) :
    untouched (PeerMirror.peerFinal pid w peer).wg = untouched w.wg := by
  by_cases zero : peer.refcount = 0
  · simp [PeerMirror.peerFinal, PeerMirror.countRecords, PeerMirror.recordCmp,
      LookupMirror.record, zero]
  · simp only [PeerMirror.peerFinal, PeerMirror.countRecords, PeerMirror.recordCmp,
      LookupMirror.record, beq_iff_eq, zero, ↓reduceIte]
    apply Prod.ext
    · simp [untouched, hasDevice]
    · funext other
      by_cases same : pid = other
      · subst other
        have found : device.peers[pid]? = some peer := hasPeer
        simp [untouched, hasDevice, found]
      · simp [untouched, hasDevice, Std.TreeMap.getElem?_insert, same]

#print axioms findNode_kernel
#print axioms peerFinal_untouched

theorem frames_peerGet_untouched (word : Option PeerId) :
    Frames (fun w => untouched w.wg) (peerGet word) := by
  intro initial history w answer points final same prior run
  cases word with
  | none =>
    rw [peer_null_run_logged] at run
    cases run
    refine ⟨same,?_⟩
    intro p member
    rcases List.mem_append.mp member with old | added
    · exact prior p old
    · have eq := List.mem_singleton.mp added
      subst p
      exact same
  | some pid =>
    have erased := peerGet_erases (some pid) history w
    rw [run] at erased
    have actual : (Source.peerGetMaybeZero (some pid)).run w = .ok (answer,final) := erased.symm
    cases hd : w.wg.dev with
    | none =>
      simp [Except.pure, Except.bind, StateT.run, liftWG, bind, StateT.bind, StateT.lift, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, WG.peerGetMaybeZero, WG.requireNotPending, WG.getPeer, WG.getDev, AmbientM.branch, monadLift, MonadLift.monadLift,  Source.peerGetMaybeZero, branch,     hd, invariant] at actual
      cases actual
    | some device =>
      cases hp : device.peers.get? pid with
      | none =>
        have absent : device.peers[pid]? = none := hp
        simp [Except.pure, Except.bind, StateT.run, liftWG, bind, StateT.bind, StateT.lift, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, WG.peerGetMaybeZero, WG.requireNotPending, WG.getPeer, WG.getDev, AmbientM.branch, monadLift, MonadLift.monadLift,  Source.peerGetMaybeZero, branch,     hd, absent,
          invariant] at actual
        cases actual
      | some peer =>
        have bound := PeerMirror.accepted_peer_bound pid w final answer device peer hd hp actual
        rw [peer_run_logged pid history w device peer hd hp bound] at run
        cases run
        refine ⟨(peerFinal_untouched pid w device peer hd hp).trans same,?_⟩
        intro p member
        rcases List.mem_append.mp member with old | added
        · exact prior p old
        · exact (congrArg untouched (peerPoints_kernel w peer p added)).trans same

theorem frames_lookup_untouched (root : Option NodeId) (bits key : Nat) :
    Frames (fun w => untouched w.wg) (lookup root bits key) := by
  unfold lookup
  apply frames_called
  apply frames_bind (frames_swapEndian untouched bits)
  intro _
  apply frames_bind (frames_findNode untouched root bits key)
  intro node
  apply frames_bind (frames_branch_kernel untouched _ _)
  intro found
  cases found with
  | false => exact frames_pure _ _
  | true =>
    cases node with
    | none =>
      apply frames_bind (frames_lift (preserves_throw _ _))
      intro _
      exact frames_pure _ _
    | some id =>
      apply frames_bind (frames_lift (preserves_getNode _ id))
      intro n
      apply frames_bind (frames_called _ (frames_peerGet_untouched n.peer))
      intro peer
      apply frames_bind (frames_branch_kernel untouched _ _)
      intro gone
      cases gone with
      | false => exact frames_pure _ _
      | true =>
        apply frames_bind (frames_lift (show Preserves (fun w => untouched w.wg)
          (unsupported "lookup retry after a dying peer" : M Unit) from by
            intro w x w' run
            cases run))
        intro _
        exact frames_pure _ _

/-- Every actual source decision/call/return point, not just the endpoint,
    frames trie nodes and all other WG fields except peer refcounts.
    Peer existence and every non-refcount peer field are included. -/
theorem lookup_untouched (root : Option NodeId) (bits key : Nat)
    (world final : World) (answer : Option PeerId) (points : List Point)
    (accepted : ((lookup root bits key).run []).run world = .ok ((answer,points),final)) :
    untouched final.wg = untouched world.wg ∧
      ∀ p ∈ points, untouched p.world.wg = untouched world.wg :=
  frames_lookup_untouched root bits key (untouched world.wg) [] world answer points final rfl
    (by intro p member; cases member) accepted

#print axioms lookup_untouched
end Binary.AllowedipsSource
