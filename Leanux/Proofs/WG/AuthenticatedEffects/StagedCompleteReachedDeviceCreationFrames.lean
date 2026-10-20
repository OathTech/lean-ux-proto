import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDeviceCreationSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointTransitionFrames

/-! Registration changes an empty setup device's epoch while retaining the
old terminal ledger. Fresh packet allocation invariants are not asserted
at the temporary setup epoch. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DeviceCreation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity TransmitSecurity Queues.RxCredits

def registered (ifindex : Nat) (w : WGWorld) : WGWorld :=
  {w with dev:=w.dev.map fun d=>{d with ifindex}}

theorem registered_tail (ifindex : Nat) (w : WGWorld) :
    (StagedEntry.view (registered ifindex w)).2=(StagedEntry.view w).2 := by
  cases dev : w.dev <;>
    simp [funext_iff,StagedEntry.view,registered,Staged.stagedAt,PacketMaterial.view,
      TxDisposition.txPackets,Packets.snapshot,Packets.deviceStore,txQueueContents,handoffTxView,dev]

theorem registered_view {initial : WGWorld} (same : StagedEntry.view w=StagedEntry.view (Lifecycle.Points.setupWorld initial)) :
    StagedEntry.view (registered ifindex w)=StagedEntry.view (freshDeviceWorld {initial with netIfindexNext:=ifindex}) := by
  have epoch:=congrArg Prod.fst same
  cases dev : w.dev with
  | none=>simp [StagedEntry.view,Packets.epoch,dev,Lifecycle.Points.setupWorld] at epoch
  | some d=>
      apply Prod.ext
      · simp [StagedEntry.view,registered,Packets.epoch,dev,freshDeviceWorld]
      · rw [registered_tail,congrArg Prod.snd same]
        rfl

theorem registered_account {initial : WGWorld} (before : Lifecycle.Points.Creating h ledger initial w)
    (prepared : (front.run w).run a=.ok ((.ok ifindex,u),c))
    (written : ((modifyDev fun d=>{d with ifindex}).run u).run c=.ok (((),v),b)) :
    CompleteCarrier.Accounted h ledger [] [] v := by
  have frontView:=(ProjectedAction.iff_run_ambient _ _ _).mp frontShape.frame _ _ _ _ _ prepared
  have setupView:=CompleteDeviceCreation.link_frame (before.setup.trans (Lifecycle.Points.setup_view initial).symm)
  have saved : CompleteCarrier.Accounted h ledger [] [] {initial with netIfindexNext:=ifindex} := before.accounted.same_view rfl
  have fresh:=Lifecycle.Points.fresh_accounted saved before.absent
  cases written
  exact fresh.same_view (registered_view (frontView.trans setupView))

theorem Point.accounted {initial : WGWorld} (before : Lifecycle.Points.Creating h ledger initial w)
    (point : Point w a v b) : CompleteCarrier.Accounted h ledger [] [] v := by
  cases point with
  | front point=>exact before.account.same_view point.frame
  | afterIndex prepared written point=>exact (registered_account before prepared written).same_view point.frame
  | returned performed=>exact (before.newlink performed).1

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DeviceCreation
