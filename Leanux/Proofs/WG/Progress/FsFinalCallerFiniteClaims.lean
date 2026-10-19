import Leanux.Proofs.WG.Progress.FsDescriptorCallerFiniteSource
import Leanux.Proofs.WG.Progress.FsEpollWaitFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Unrestricted campaign projections of native duplication, close and
epoll-wait finite evaluators; exact native equations retain every Stop. -/

theorem original_ksysDup3_finite (oldfd newfd : Nat) (flags : UInt32) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.ksysDup3 oldfd newfd flags)) (liftFS (ksysDup3 oldfd newfd flags)) := by
  rw [ksysDup3_source]
  intro w pre
  rfl

theorem original_sysDup_finite (fildes : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.sysDup fildes)) (liftFS (sysDup fildes)) := by
  rw [sysDup_source]
  intro w pre
  rfl

theorem original_sysClose_finite (fd : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.sysClose fd)) (liftFS (sysClose fd)) := by
  rw [sysClose_source]
  intro w pre
  rfl

theorem original_epDeliverEvent_finite (ep : EpId) (epiId : EpiId) (pt : PollTable) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.epDeliverEvent ep epiId pt)) (liftFS (epDeliverEvent ep epiId pt)) := by
  rw [epDeliverEvent_source]
  intro w pre
  rfl

theorem original_epSendEvents_finite (ep : EpId) (maxevents : Int) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.epSendEvents ep maxevents)) (liftFS (epSendEvents ep maxevents)) := by
  rw [epSendEvents_source]
  intro w pre
  rfl

theorem original_epPoll_finite (ep : EpId) (maxevents : Int) (timeout : Option Timespec64) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.epPoll ep maxevents timeout)) (liftFS (epPoll ep maxevents timeout)) := by
  rw [epPoll_source]
  intro w pre
  rfl

theorem original_doEpollWait_finite (epfd : Nat) (maxevents : Int) (to : Option Timespec64) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.doEpollWait epfd maxevents to)) (liftFS (doEpollWait epfd maxevents to)) := by
  rw [doEpollWait_source]
  intro w pre
  rfl

theorem original_sysEpollWait_finite (epfd : Nat) (maxevents timeout : Int) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.sysEpollWait epfd maxevents timeout)) (liftFS (sysEpollWait epfd maxevents timeout)) := by
  rw [sysEpollWait_source]
  intro w pre
  rfl


end Leanux.Proofs.WG.Progress.FsFinite
