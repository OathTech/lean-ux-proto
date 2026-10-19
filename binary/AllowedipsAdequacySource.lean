import SourceAdapter
import AllowedipsSourceSelected

namespace Binary.AllowedipsSource
open Leanux Leanux.WG MirrorHistory

/-- Acceptance of the source suffix supplies the live selected peer and
    the arithmetic bound used by the actual helper. Dead peers remain in
    the entry domain; this suffix refuses a dying selected peer explicitly. -/
theorem suffix_live (id : NodeId) (history points : List Point)
    (world final : World) (answer : Option PeerId)
    (accepted : ((searchSuffix (some id)).run history).run world =
      .ok ((answer,points),final)) :
    ∃ device node pid peer helperPoints,
      world.wg.dev = some device ∧ device.nodes.get? id = some node ∧
      node.peer = some pid ∧ device.peers.get? pid = some peer ∧
      answer = some pid ∧ peer.refcount ≠ 0 ∧ peer.refcount+1 < 2^31 ∧
      ((peerGet (some pid)).run
        (history ++ [⟨.call "wg_peer_get_maybe_zero",world⟩])).run world =
        .ok ((some pid,helperPoints), PeerMirror.peerFinal pid world peer) ∧
      final = LookupMirror.record (PeerMirror.peerFinal pid world peer) .lookupPeerGone false ∧
      points = helperPoints ++ [⟨.returned "wg_peer_get_maybe_zero",PeerMirror.peerFinal pid world peer⟩] ++
        [⟨.decision .lookupPeerGone,final⟩] := by
  obtain ⟨node,readPoints,readWorld,read,rest⟩ := accepted_bind _ _ _ _ _ accepted
  have readResult : ∃ device, world.wg.dev = some device ∧ device.nodes.get? id = some node ∧
      readPoints = history ∧ readWorld = world := by
    cases hd : world.wg.dev with
    | none =>
      simp [StateT.run_lift,Source.getNode_eq,Source.getDev_eq,StateT.run_bind,hd,invariant] at read
      cases read
    | some device =>
      cases hn : device.nodes.get? id with
      | none =>
        have absent : device.nodes[id]? = none := hn
        simp [StateT.run_lift,Source.getNode_eq,Source.getDev_eq,StateT.run_bind,hd,absent,invariant] at read
        cases read
      | some n =>
        have present : device.nodes[id]? = some n := hn
        have eq : ((n,history),world) = ((node,readPoints),readWorld) := by
          simp [StateT.run_lift,Source.getNode_eq,Source.getDev_eq,StateT.run_bind,hd,present] at read
          exact Except.ok.inj read
        obtain ⟨⟨rfl,rfl⟩,rfl⟩ := Prod.mk.inj eq
        exact ⟨device,rfl,hn,rfl,rfl⟩
  obtain ⟨device,hd,hn,readPointsEq,readWorldEq⟩ := readResult
  subst readPoints readWorld
  obtain ⟨peerAnswer,helperPoints,helperWorld,helper,after⟩ := accepted_bind _ _ _ _ _ rest
  obtain ⟨same,live,finalEq,pointsEq⟩ := afterPeer_accepted peerAnswer answer _ _ _ _ after
  obtain ⟨inner,innerRun,helperEq⟩ := called_accepted helper
  have actual : (Source.peerGetMaybeZero node.peer).run world = .ok (peerAnswer,helperWorld) := by
    have erased := peerGet_erases node.peer (history ++ [⟨.call "wg_peer_get_maybe_zero",world⟩]) world
    rw [innerRun] at erased
    exact erased.symm
  cases word : node.peer with
  | none =>
    rw [word,PeerMirror.peer_null_run] at actual
    have eq := (Prod.mk.inj (Except.ok.inj actual)).1
    rw [←eq] at live
    cases live
  | some pid =>
    rw [word] at actual
    cases hp : device.peers.get? pid with
    | none =>
      have absent : device.peers[pid]? = none := hp
      simp [Except.pure, Except.bind, StateT.run, liftWG, bind, StateT.bind, StateT.lift, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, WG.peerGetMaybeZero, WG.requireNotPending, WG.getPeer, WG.getDev, AmbientM.branch, monadLift, MonadLift.monadLift,  Source.peerGetMaybeZero,branch,hd,absent,invariant] at actual
      cases actual
    | some peer =>
      have bound := PeerMirror.accepted_peer_bound pid world helperWorld peerAnswer device peer hd hp actual
      obtain ⟨result,worldEq⟩ := PeerMirror.accepted_peer_result pid world helperWorld peerAnswer device peer hd hp actual
      have nonzero : peer.refcount ≠ 0 := by
        intro zero
        rw [result,ite_eq_left zero] at live
        cases live
      have resultEq : peerAnswer = some pid := by simpa only [ite_eq_right nonzero] using result
      refine ⟨device,node,pid,peer,inner,hd,hn,word,hp,same.symm.trans resultEq,nonzero,bound,?_,?_,?_⟩
      · simpa only [word,resultEq,worldEq] using innerRun
      · simpa only [worldEq] using finalEq
      · simpa only [helperEq,worldEq] using pointsEq

#print axioms suffix_live
end Binary.AllowedipsSource
