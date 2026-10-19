import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerRetirementObserver

/-! Fixed native release prefixes retain the original observer receipt and
finish. In particular the post-erasure cut owes a receipt about the original
entry world, not about a fresh release from the erased world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
open Leanux Leanux.WG Leanux.Proofs.Logged
open CausalJournal HandshakeSecurity.StagedDisposal

inductive Site where
  | decremented | unlinked | erased

def prefixAt (site : Site) (peer : Option PeerId) : WG.M Cached :=
  match site with
  | .decremented => decrementTo peer
  | .unlinked => unlinkTo peer
  | .erased => releaseCut peer

def tailAt (site : Site) (value : Cached) : WG.M Cached :=
  match site with
  | .decremented => decrementTail value
  | .unlinked => eraseTail value
  | .erased => pure value

theorem point_factor (site : Site) (peer : Option PeerId) :
    releaseCut peer=prefixAt site peer >>= tailAt site := by
  cases site with
  | decremented => exact release_decrement_factor peer
  | unlinked => exact release_unlink_factor peer
  | erased => exact (bind_pure _).symm

def remaining (peer : Option PeerId) (origin : WGWorld) (clock : Ambient)
    (native : WG.M Cached) : WGPrefix CausalJournal.Event Unit :=
  fun w a => ExceptT.mk fun history =>
    match (native.run w).run a with
    | .error stop => (.error stop,history)
    | .ok ((value,v),b) =>
        let last := history++[releaseEvent peer value origin v clock b]
        match value with
        | none => (.ok (((),v),b),last)
        | some (pid,p) => (((releaseFinish pid p).run v).run b,last)

theorem point_continuation
    (performed : ((prefixAt site peer).run w).run a=.ok ((value,v),b)) :
    runWGPrefix (CausalJournal.peerRelease peer) w a history=
      runWGPrefix (remaining peer w a (tailAt site value)) v b history := by
  have source := StagedAdmission.Front.put_run peer w a history
  change runWGPrefix (CausalJournal.peerRelease peer) w a history=_ at source
  rw [source,point_factor site,StateT.run_bind,StateT.run_bind,performed]
  rfl

theorem point_lifted
    (performed : ((prefixAt site peer).run w.wg).run w.ambient=.ok ((value,v),b)) :
    runPrefix (liftWGObserver (CausalJournal.peerRelease peer)) w history=
      runPrefix (liftWGObserver (remaining peer w.wg w.ambient (tailAt site value)))
        {w with wg:=v,ambient:=b} history := by
  rw [liftWGObserver_run,liftWGObserver_run,point_continuation performed]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
