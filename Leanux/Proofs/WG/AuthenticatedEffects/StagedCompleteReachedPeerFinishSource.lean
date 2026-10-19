import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerRetirementContinuation

/-! The original post-receipt release suffix checks cached timers, retires
work identities in Ambient, then retires timer identities in WGWorld. These
are separate native writes; neither settles or creates a packet obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Finish
open Leanux Leanux.WG Leanux.Proofs.Logged
open HandshakeSecurity.StagedDisposal

def pending (p : Peer) : Option PeerTimer :=
  PeerTimer.all.find? (fun timer => p.timerPending timer || (p.wheel timer).isSome)

def guard (pid : PeerId) (p : Peer) : WG.M Unit := do
  if let some timer := pending p then
    invariant s!"peer {pid} released with its {repr timer} timer pending"

def workClock (pid : PeerId) (a : Ambient) : Ambient :=
  {a with unitPeers := a.unitPeers.filter fun (e : Nat × Nat × Nat) =>
    !((Worker.all.find? (·.index == e.2.1)).any Worker.perPeer && e.2.2 == pid)}

def timersWorld (pid : PeerId) (w : WGWorld) : WGWorld :=
  {w with timerUnits := w.timerUnits.filter (·.2.1 != pid)}

def work (pid : PeerId) : WG.M Unit := modifyAmbient (workClock pid)
def timers (pid : PeerId) : WG.M Unit := modify (timersWorld pid)

theorem source_factor (pid : PeerId) (p : Peer) :
    releaseFinish pid p=(do guard pid p; work pid; timers pid) := by
  cases found : PeerTimer.all.find? (fun timer => p.timerPending timer || (p.wheel timer).isSome) with
  | none => simp only [releaseFinish,guard,pending,found]; rfl
  | some timer => simp only [releaseFinish,guard,pending,found]; rfl

inductive Site where
  | checked | workRetired | timersRetired

def prefixAt (site : Site) (pid : PeerId) (p : Peer) : WG.M Unit := do
  guard pid p
  match site with
  | .checked => pure ()
  | .workRetired => work pid
  | .timersRetired => work pid; timers pid

def tailAt (site : Site) (pid : PeerId) : WG.M Unit :=
  match site with
  | .checked => do work pid; timers pid
  | .workRetired => timers pid
  | .timersRetired => pure ()

theorem point_factor (site : Site) (pid : PeerId) (p : Peer) :
    releaseFinish pid p=(do prefixAt site pid p; tailAt site pid) := by
  rw [source_factor]
  cases site <;> simp only [prefixAt,tailAt,bind_assoc,bind_pure_unit]

theorem point_continuation
    (performed : ((prefixAt site pid p).run w).run a=.ok (((),v),b)) :
    ((releaseFinish pid p).run w).run a=((tailAt site pid).run v).run b := by
  rw [point_factor site,StateT.run_bind,StateT.run_bind,performed]
  rfl

theorem release_continuation
    (native : ((releaseCut peer).run w).run a=.ok ((some (pid,p),v),b))
    (performed : ((prefixAt site pid p).run v).run b=.ok (((),g),c)) :
    runWGPrefix (CausalJournal.peerRelease peer) w a history=
      runWGPrefix (liftWGPrefix (tailAt site pid)) g c
        (history++[releaseEvent peer (some (pid,p)) w v a b]) := by
  rw [release_recorded native,point_continuation performed,runWGPrefix_lift]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Finish
