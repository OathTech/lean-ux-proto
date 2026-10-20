import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerPointFrames

/-! Fixed native points for a raw peerPut call. This family emits no observer
receipt. Its continuation follows the same native cut and finish source as
the observed release, including paths that later stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RawPeer
open Leanux Leanux.WG Leanux.Proofs.Logged
open HandshakeSecurity.StagedDisposal PeerRetirement

def finish : Cached → WG.M Unit
  | none=>pure ()
  | some (pid,p)=>releaseFinish pid p

theorem source (peer : Option PeerId) : peerPut peer=releaseCut peer >>= finish := release_factor peer

inductive Point (peer : Option PeerId) (w : WGWorld) (a : Ambient) : WGWorld → Ambient → Type 1 where
  | entry : Point peer w a w a
  | native (stage : Points.Stage) (value : stage.Result)
      (performed : ((stage.prefix peer).run w).run a=.ok ((value,v),b)) : Point peer w a v b
  | cut (value : Cached)
      (performed : ((releaseCut peer).run w).run a=.ok ((value,v),b)) : Point peer w a v b
  | finish (pid : PeerId) (p : Peer) (site : Finish.Site)
      (cut : ((releaseCut peer).run w).run a=.ok ((some (pid,p),v),b))
      (performed : ((Finish.prefixAt site pid p).run v).run b=.ok (((),u),c)) : Point peer w a u c
  | returned (performed : ((peerPut peer).run w).run a=.ok (((),v),b)) : Point peer w a v b

def Point.remainder (point : Point peer w a v b) : WG.M Unit :=
  match point with
  | .entry=>peerPut peer
  | .native stage value _=>stage.tail value >>= RawPeer.finish
  | .cut value _=>RawPeer.finish value
  | .finish pid _ site _ _=>Finish.tailAt site pid
  | .returned _=>pure ()

theorem Point.continuation (point : Point peer w a v b) :
    ((peerPut peer).run w).run a=((point.remainder).run v).run b := by
  cases point with
  | entry=>rfl
  | native stage value performed=>
    rw [source,stage.factor,bind_assoc,StateT.run_bind,StateT.run_bind,performed]
    rfl
  | cut value performed=>
    rw [source,StateT.run_bind,StateT.run_bind,performed]
    rfl
  | finish pid p site cut performed=>
    rw [source,StateT.run_bind,StateT.run_bind,cut]
    exact Finish.point_continuation performed
  | returned performed=>exact performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RawPeer
