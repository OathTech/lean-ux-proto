import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerFinishSource

/-! Each native identity-retirement write keeps the packet projection and
the same ledger. Ambient work identities and timer identities are separate
from packet stores; the proof states that projection directly. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Finish
open Leanux Leanux.WG Leanux.Proofs.Logged
open HandshakeSecurity.StagedDisposal CompleteCarrier

theorem work_run (pid : PeerId) (w : WGWorld) (a : Ambient) :
    ((work pid).run w).run a=.ok (((),w),workClock pid a) := rfl

theorem timers_run (pid : PeerId) (w : WGWorld) (a : Ambient) :
    ((timers pid).run w).run a=.ok (((),timersWorld pid w),a) := rfl

theorem timer_view (pid : PeerId) (w : WGWorld) :
    StagedEntry.view (timersWorld pid w)=StagedEntry.view w := rfl

theorem timer_accounted (before : Accounted history ledger debts locals w) :
    Accounted history ledger debts locals (timersWorld pid w) :=
  ⟨before.entry.same_view (timer_view pid w),before.complete⟩

theorem guard_ok (quiet : pending p=none) (pid : PeerId) (w : WGWorld) (a : Ambient) :
    ((guard pid p).run w).run a=.ok (((),w),a) := by
  simp only [guard,quiet]
  rfl

theorem guard_stopped (busy : pending p=some timer) (pid : PeerId) (w : WGWorld) (a : Ambient) :
    ((guard pid p).run w).run a=
      .error (.invariant s!"peer {pid} released with its {repr timer} timer pending") := by
  simp only [guard,busy]
  rfl

def atWorld (site : Site) (pid : PeerId) (w : WGWorld) : WGWorld :=
  match site with
  | .checked | .workRetired => w
  | .timersRetired => timersWorld pid w

def atClock (site : Site) (pid : PeerId) (a : Ambient) : Ambient :=
  match site with
  | .checked => a
  | .workRetired | .timersRetired => workClock pid a

theorem prefix_run (quiet : pending p=none) (site : Site) (pid : PeerId) (w : WGWorld) (a : Ambient) :
    ((prefixAt site pid p).run w).run a=.ok (((),atWorld site pid w),atClock site pid a) := by
  cases site <;> simp only [prefixAt,StateT.run_bind,guard_ok quiet,work_run,timers_run,atWorld,atClock] <;> rfl

theorem prefix_accounted (before : Accounted history ledger debts locals w) (site : Site) :
    Accounted history ledger debts locals (atWorld site pid w) := by
  cases site with
  | checked => exact before
  | workRetired => exact before
  | timersRetired => exact timer_accounted before

theorem stopped (busy : pending p=some timer) (pid : PeerId) (w : WGWorld) (a : Ambient) :
    ((releaseFinish pid p).run w).run a=
      .error (.invariant s!"peer {pid} released with its {repr timer} timer pending") := by
  rw [source_factor,StateT.run_bind,StateT.run_bind,guard_stopped busy]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Finish
