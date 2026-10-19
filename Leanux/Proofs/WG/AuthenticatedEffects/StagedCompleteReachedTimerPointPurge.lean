import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerPointCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerRetirementObserver

/-! Purge points retain the two distinct native writes and the original
cohort until its total receipt suffix, then settle that cohort exactly once. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points.Purge
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
open PeerRetirement

inductive Phase where | read | charged | cleared | recorded

def state (pid : PeerId) (p : Peer) (d : Device) (w : World) : Phase → World
  | .read => w
  | .charged => {w with wg := charged p d w.wg}
  | .cleared | .recorded => {w with wg := cleared pid p d w.wg}

def receipt (pid : PeerId) (p : Peer) (d : Device) (w : World) : Event :=
  purgeEvent pid w.wg (cleared pid p d w.wg) w.ambient w.ambient

def history (pid : PeerId) (p : Peer) (d : Device) (w : World) (h : History) : Phase → History
  | .recorded => h ++ [receipt pid p d w]
  | _ => h

def sourcePrefix (pid : PeerId) : Phase → PrefixM Event Unit
  | .read => wg (getPeer pid) >>= fun _ => pure ()
  | .charged => wg (purgeChargeTo pid) >>= fun _ => pure ()
  | .cleared => wg (purgeStagedPackets pid)
  | .recorded => liftWGObserver (stagedPurge pid)

def suffix (pid : PeerId) (p : Peer) (d : Device) (w : World) : Phase → PrefixM Event Unit
  | .read => do wg (purgeCharge p); wg (purgeClear pid p); emitPrefix (receipt pid p d w)
  | .charged => do wg (purgeClear pid p); emitPrefix (receipt pid p d w)
  | .cleared => emitPrefix (receipt pid p d w)
  | .recorded => pure ()

theorem native_run (action : WG.M α) (w : World) (h : History) :
    runPrefix (wg action) w h =
      match ((action.run w.wg).run w.ambient) with
      | .error reason => (.error reason,h)
      | .ok ((value,v),a) => (.ok (value,{w with wg:=v,ambient:=a}),h) :=
  Wheel.Points.native_run action w h

theorem prefix_run (device : w.wg.dev = some d) (resident : d.peers[pid]? = some p) (phase : Phase) :
    runPrefix (sourcePrefix pid phase) w h = (.ok ((),state pid p d w phase),history pid p d w h phase) := by
  cases phase with
  | read =>
    rw [sourcePrefix,runPrefix_bind,native_run]
    have read : ((getPeer pid).run w.wg).run w.ambient = .ok ((p,w.wg),w.ambient) := by
      simp [getPeer,getDev,device,resident]
    rw [read]
    rfl
  | charged =>
    rw [sourcePrefix,runPrefix_bind,native_run,purge_charge_prefix device resident]
    rfl
  | cleared =>
    rw [sourcePrefix,native_run,purge_clear_prefix device resident]
    rfl
  | recorded =>
    rw [sourcePrefix,liftWGObserver_run,purge_recorded device resident]
    rfl

theorem suffix_run (device : w.wg.dev = some d) (phase : Phase) :
    runPrefix (suffix pid p d w phase) (state pid p d w phase) (history pid p d w h phase) =
      (.ok ((),state pid p d w .recorded),history pid p d w h .recorded) := by
  cases phase with
  | read =>
    rw [suffix,runPrefix_bind,native_run]
    change (match (((purgeCharge p).run w.wg).run w.ambient) with
      | .error reason => ((Except.error reason : Result Unit),h)
      | .ok ((value,v),a) => runPrefix (do wg (purgeClear pid p); emitPrefix (receipt pid p d w)) {w with wg:=v,ambient:=a} h) = _
    rw [charge_run device]
    simp only []
    rw [runPrefix_bind,native_run,clear_run]
    rfl
  | charged =>
    rw [suffix,runPrefix_bind,native_run]
    change (match (((purgeClear pid p).run (charged p d w.wg)).run w.ambient) with
      | .error reason => ((Except.error reason : Result Unit),h)
      | .ok ((value,v),a) => runPrefix (emitPrefix (receipt pid p d w)) {w with wg:=v,ambient:=a} h) = _
    rw [clear_run]
    rfl
  | cleared => rfl
  | recorded => rfl

theorem continuation (device : w.wg.dev = some d) (resident : d.peers[pid]? = some p) (phase : Phase) :
    runPrefix (liftWGObserver (stagedPurge pid)) w h =
      runPrefix (suffix pid p d w phase) (state pid p d w phase) (history pid p d w h phase) :=
  (prefix_run device resident .recorded).trans (suffix_run device phase).symm
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points.Purge
