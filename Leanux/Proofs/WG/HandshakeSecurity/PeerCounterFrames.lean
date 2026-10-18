import Leanux.Proofs.WG.HandshakeSecurity.FreshnessHandshakeFrames

/-! Allocation-frontier frames for the native initiation source. The frontier
is separate from the retained timestamp projection: it is needed to distinguish
freshly allocated peers from earlier occupants of a numeric peer slot. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerCounter
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

abbrev Same (action : WG.M α) := SameView WGWorld.peerCounter action

theorem update (pid : PeerId) (f : Peer → Peer) :
    Same (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,ambient,getter,setter⟩ := run
  obtain ⟨rfl,rfl,_,_,_⟩ := Queues.getPeer_normal pid w read p a ambient getter
  cases setter
  rfl

theorem peer_put (peer : Option PeerId) : Same (peerPut peer) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  exact ((ProjectedAction.iff_run_ambient _ _ _).mp (Peers.peerPut_retained peer) w a x v b run).1

theorem maybe_peer (peer : Option PeerId) : Same (peerGetMaybeZero peer) :=
  SameView.factor (show SameView Peers.snapshot (peerGetMaybeZero peer) from
    Peers.peerGetMaybeZero_samePeerSnapshot peer) (·.frontier)

theorem lookup (key : Key) : Same (pubkeyLookup key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  cases hd : w.dev with
  | none => simp [pubkeyLookup,getDev,hd,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    have equation : ((pubkeyLookup key).run w).run a =
        ((peerGetMaybeZero ((d.peerHashtable.find? (·.1 == key)).map (·.2))).run w).run
          (CounterWindow.record a .pubkeyLookupMatch
            ((d.peerHashtable.find? (·.1 == key)).map (·.2)).isSome) := by
      simp [pubkeyLookup,getDev,hd,branch,AmbientM.branch]
      rfl
    rw [equation] at run
    exact (ProjectedAction.iff_run_ambient _ _ _).mp (maybe_peer _) w _ x v b run

theorem out (peer ret : Option PeerId) : Same (Queues.RxCredits.HandshakeLoans.initiationOut peer ret) := by
  unfold Queues.RxCredits.HandshakeLoans.initiationOut
  apply SameView.bind (show Same (branch .consumeFailedPut ret.isNone) from
    fun initial => hoare_liftAmbient (AmbientM.branch .consumeFailedPut ret.isNone) (fun w : WGWorld => w.peerCounter = initial))
  intro ignored
  dsimp only
  split
  · apply SameView.bind (peer_put peer)
    intro _
    exact SameView.pure _ _
  · exact SameView.pure _ _

end Leanux.Proofs.WG.HandshakeSecurity.PeerCounter
