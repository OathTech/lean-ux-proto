import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTimerZero
import Leanux.Proofs.WG.Queues.HolderTimerCallbacks

/-! Timer-facing staging and queued-send transitions absorb the exact native
handoff delta into both bounds, without selecting a second holder witness. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits Std.Do
open DurableHolders

theorem Account.staged (pid : PeerId) (account : Account h cs loans w)
    (run : ((sendStagedPackets pid).run w).run a = .ok (((),v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧ Account (h.absorb delta) cs loans v := by
  obtain ⟨delta,step,funded,stable⟩ := HolderTimers.staged_funded pid
    account.funded account.stable a b run
  have upper : Upper h cs (loans ++ []) w := by simpa using account.upper
  exact ⟨delta,step,⟨funded,by simpa using upper.handoff step,stable⟩⟩

theorem Account.queued (pid : PeerId) (retry : Bool) (account : Account h cs loans w)
    (run : ((sendQueuedHandshakeInitiation pid retry).run w).run a = .ok (((),v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧ Account (h.absorb delta) cs loans v := by
  obtain ⟨delta,step,funded,stable⟩ := HolderTimers.sendQueued_funded pid retry
    account.funded account.stable a b run
  have upper : Upper h cs (loans ++ []) w := by simpa using account.upper
  exact ⟨delta,step,⟨funded,by simpa using upper.handoff step,stable⟩⟩

theorem ExactBoundary.staged (pid : PeerId) :
    Preserves (ExactBoundary cs loans) (sendStagedPackets pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  cases x
  obtain ⟨h,account⟩ := hi
  obtain ⟨delta,_,kept⟩ := account.staged pid run
  exact ⟨h.absorb delta,kept⟩

theorem ExactBoundary.queued (pid : PeerId) (retry : Bool) :
    Preserves (ExactBoundary cs loans) (sendQueuedHandshakeInitiation pid retry) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  cases x
  obtain ⟨h,account⟩ := hi
  obtain ⟨delta,_,kept⟩ := account.queued pid retry run
  exact ⟨h.absorb delta,kept⟩

namespace TimerFrames

theorem modify_account (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀p,(f p).internalId=p.internalId) (count : ∀p,(f p).refcount=p.refcount)
    (rx : ∀p,(f p).rxQueue=p.rxQueue) (napi : ∀p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀p kid,(f p).keypairCurrent=some kid → p.keypairCurrent=some kid)
    (tx : ∀p,(f p).txQueue.all=p.txQueue.all) :
    Preserves (Account h cs loans) (do let p ← getPeer pid; setPeer pid (f p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b account run
  have kept := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.modify_peer)
      pid f stamp count rx napi current tx) w a x v b ⟨account.funded,account.stable⟩ run
  exact ⟨kept.1,account.upper.peer_view ((ProjectedAction.iff_run_ambient _ _ _).mp
    (WorkFrames.update_peer pid f stamp count rx) w a x v b run),kept.2⟩

theorem modify_boundary (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀p,(f p).internalId=p.internalId) (count : ∀p,(f p).refcount=p.refcount)
    (rx : ∀p,(f p).rxQueue=p.rxQueue) (napi : ∀p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀p kid,(f p).keypairCurrent=some kid → p.keypairCurrent=some kid)
    (tx : ∀p,(f p).txQueue.all=p.txQueue.all) :
    Preserves (ExactBoundary cs loans) (do let p ← getPeer pid; setPeer pid (f p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  obtain ⟨h,account⟩ := hi
  exact ⟨h,(hoare_iff_run_ambient _ _ _).mp
    (modify_account pid f stamp count rx napi current tx) w a x v b account run⟩

/-- The setter uses the peer actually read from this input world; arbitrary
historical reads cannot discharge this entry contract. -/
theorem source_modify_account (account : Account h cs loans w) (hd : w.dev = some d)
    (hp : d.peers[pid]? = some p) (f : Peer → Peer)
    (stamp : ∀p,(f p).internalId=p.internalId) (count : ∀p,(f p).refcount=p.refcount)
    (rx : ∀p,(f p).rxQueue=p.rxQueue) (napi : ∀p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀p kid,(f p).keypairCurrent=some kid → p.keypairCurrent=some kid)
    (tx : ∀p,(f p).txQueue.all=p.txQueue.all) (a b : Ambient)
    (run : ((setPeer pid (f p)).run w).run a = .ok ((x,v),b)) :
    Account h cs loans v := by
  apply (hoare_iff_run_ambient _ _ _).mp
    (modify_account pid f stamp count rx napi current tx) w a x v b account
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨p,w,a,by simp [getPeer,getDev,hd,hp],run⟩

theorem source_modify (account : ExactBoundary cs loans w) (hd : w.dev = some d)
    (hp : d.peers[pid]? = some p) (f : Peer → Peer)
    (stamp : ∀p,(f p).internalId=p.internalId) (count : ∀p,(f p).refcount=p.refcount)
    (rx : ∀p,(f p).rxQueue=p.rxQueue) (napi : ∀p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀p kid,(f p).keypairCurrent=some kid → p.keypairCurrent=some kid)
    (tx : ∀p,(f p).txQueue.all=p.txQueue.all) (a b : Ambient)
    (run : ((setPeer pid (f p)).run w).run a = .ok ((x,v),b)) :
    ExactBoundary cs loans v := by
  obtain ⟨h,account⟩ := account
  exact ⟨h,source_modify_account account hd hp f stamp count rx napi current tx a b run⟩

theorem read_boundary (pid : PeerId) : Preserves (ExactBoundary cs loans) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  exact (getPeer_normal pid w v p a b run).1 ▸ hi

theorem control {action : WG.M α}
    (same : SameView (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.view) action)
    (frame : ∀ initial, Preserves (Frame initial) action) :
    Preserves (Account h cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b account run
  apply WorkFrames.fixed _ frame
    (fun _ _ => (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.control_keeps) same)
    account run
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  have view := (ProjectedAction.iff_run_ambient _ _ _).mp same w a x v b run
  have carrier := ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrier_factor) v).trans
    ((congrArg (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrierOf) view).trans
      ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrier_factor) w).symm)
  exact congrArg Prod.fst carrier

theorem exists_account {action : WG.M α}
    (keeps : ∀ h, Preserves (Account h cs loans) action) :
    Preserves (ExactBoundary cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  obtain ⟨h,account⟩ := hi
  exact ⟨h,(hoare_iff_run_ambient _ _ _).mp (keeps h) w a x v b account run⟩

end TimerFrames
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
