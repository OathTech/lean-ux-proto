import Leanux.Proofs.WG.RetirementSecurity.SessionFunding

/-! Session suffix frames: handshake zeroing changes the actual peer's
handshake fields, while index operations preserve key-reference funding. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes

def zeroedPeer (p : Peer) : Peer :=
  {p with ephemeralPrivate := List.replicate 32 0, remoteEphemeral := List.replicate 32 0, hash := List.replicate 32 0, chainingKey := List.replicate 32 0, remoteIndex := 0, handshakeState := 0}

theorem zero_peer_account (pid : PeerId) (p : Peer) (credits : Credits.Ledger) :
    Hoare (handshakeZero pid) (PeerAccount pid p credits)
      (fun _ => PeerAccount pid (zeroedPeer p) credits) :=
  update_peer_account pid p credits zeroedPeer

theorem index_peer_account (action : IndexM α) (pid : PeerId) (p : Peer)
    (credits : Credits.Ledger) :
    Preserves (PeerAccount pid p credits) (liftIndex action) := by
  apply hoare_liftIndex action
  intro w d table hi device
  constructor
  · simpa [peerAt,device] using hi.1
  · intro allocation
    simpa [Credits.balance,keyAt,device] using hi.2 allocation

theorem keyAt_of_material (same : Origins.view v = Origins.view w) (id : KeypairId) :
    keyAt v id = keyAt w id := by
  have keys := congrArg (fun view => view.bind fun fields => fields.2 id) same
  simpa only [Origins.view,keyAt,Option.bind_map,Function.comp_def] using keys

theorem zero_keyAt (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((handshakeZero pid).run w).run a = .ok (((),v),b)) (id : KeypairId) :
    keyAt v id = keyAt w id :=
  keyAt_of_material ((ProjectedAction.iff_run_ambient _ _ _).mp
    (Origins.handshakeZero_view pid) w a () v b run) id

end Leanux.Proofs.WG.RetirementSecurity
