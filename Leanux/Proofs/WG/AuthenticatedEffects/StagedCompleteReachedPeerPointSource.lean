import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerFinishCoverage

/-! Fixed native source points of the original peer-release observer. The
receipt retains its original invocation even after the peer has been erased.
No arbitrary factorization can construct a point. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Points
open Leanux Leanux.WG Leanux.Proofs.Logged
open CausalJournal HandshakeSecurity.StagedDisposal

inductive Stage where
  | read | decrement | test | unlink | checked

abbrev Stage.Result : Stage → Type
  | .test => Tested
  | _ => Cached

def checkedTo (peer : Option PeerId) : WG.M Cached := do
  let cached ← unlinkTo peer
  match cached with
  | none => pure none
  | some (_,p) => queueGuard p; pure cached

def eraseAfter : Cached → WG.M Cached
  | none => pure none
  | some (pid,p) => do erase pid p; pure (some (pid,p))

def Stage.prefix (stage : Stage) (peer : Option PeerId) : WG.M stage.Result :=
  match stage with
  | .read => readRelease peer
  | .decrement => decrementTo peer
  | .test => testTo peer
  | .unlink => unlinkTo peer
  | .checked => checkedTo peer

def Stage.tail (stage : Stage) : stage.Result → WG.M Cached :=
  match stage with
  | .read => readTail
  | .decrement => decrementTail
  | .test => testTail
  | .unlink => eraseTail
  | .checked => eraseAfter

theorem checked_factor (peer : Option PeerId) :
    releaseCut peer=checkedTo peer >>= eraseAfter := by
  rw [release_unlink_factor]
  simp only [checkedTo,bind_assoc]
  congr 1
  funext cached
  cases cached with
  | none => rfl
  | some pair =>
    obtain ⟨pid,p⟩ := pair
    simp only [eraseTail,eraseAfter,bind_assoc,pure_bind]

theorem Stage.factor (stage : Stage) (peer : Option PeerId) :
    releaseCut peer=stage.prefix peer >>= stage.tail := by
  cases stage with
  | read => exact release_read_factor peer
  | decrement => exact release_decrement_factor peer
  | test => exact release_test_factor peer
  | unlink => exact release_unlink_factor peer
  | checked => exact checked_factor peer

abbrev History := List CausalJournal.Event

inductive Point (peer : Option PeerId) (w : WGWorld) (a : Ambient) (h : History) :
    WGWorld → Ambient → History → Type 1 where
  | entry : Point peer w a h w a h
  | native (stage : Stage) (value : stage.Result)
      (performed : ((stage.prefix peer).run w).run a=.ok ((value,v),b)) :
      Point peer w a h v b h
  | erased (value : Cached)
      (performed : ((releaseCut peer).run w).run a=.ok ((value,v),b)) :
      Point peer w a h v b h
  | recorded (value : Cached)
      (performed : ((releaseCut peer).run w).run a=.ok ((value,v),b)) :
      Point peer w a h v b (h++[releaseEvent peer value w v a b])
  | finish (pid : PeerId) (p : Peer) (site : Finish.Site)
      (native : ((releaseCut peer).run w).run a=.ok ((some (pid,p),v),b))
      (performed : ((Finish.prefixAt site pid p).run v).run b=.ok (((),u),c)) :
      Point peer w a h u c (h++[releaseEvent peer (some (pid,p)) w v a b])

def finishAction : Cached → WGPrefix CausalJournal.Event Unit
  | none => pure ()
  | some (pid,p) => liftWGPrefix (releaseFinish pid p)

def Point.remainder {peer w a h u b middle} (point : Point peer w a h u b middle) : WGPrefix CausalJournal.Event Unit :=
  match point with
  | .entry => CausalJournal.peerRelease peer
  | .native stage value _ => remaining peer w a (stage.tail value)
  | .erased value _ => remaining peer w a (pure value)
  | .recorded value _ => finishAction value
  | .finish pid _ site _ _ => liftWGPrefix (Finish.tailAt site pid)

theorem native_continuation {stage : Stage} {value : stage.Result}
    (performed : ((stage.prefix peer).run w).run a=.ok ((value,v),b)) :
    runWGPrefix (CausalJournal.peerRelease peer) w a h=
      runWGPrefix (remaining peer w a (stage.tail value)) v b h := by
  have source := StagedAdmission.Front.put_run peer w a h
  change runWGPrefix (CausalJournal.peerRelease peer) w a h=_ at source
  rw [source,stage.factor,StateT.run_bind,StateT.run_bind,performed]
  rfl

theorem Point.continuation (point : Point peer w a h u b middle) :
    runWGPrefix (CausalJournal.peerRelease peer) w a h=
      runWGPrefix point.remainder u b middle := by
  cases point with
  | entry => rfl
  | native stage value performed => exact native_continuation performed
  | erased value performed => exact point_continuation (site:=.erased) performed
  | recorded value performed =>
    cases value with
    | none => exact release_none_recorded performed
    | some pair =>
      obtain ⟨pid,p⟩ := pair
      exact release_recorded performed
  | finish pid p site native performed => exact Finish.release_continuation native performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Points
