import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTimerCallbacks

/-! The zero-material timer queues clear work without clearing keys itself.
Its refusal repays the reference acquired by this same invocation, so the
full entry view survives both native normal branches. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ZeroTimer
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open Queues.RxCredits

def fromBorrow (s : WGStoreView × (PeerId → Option Peer)) :=
  let static := StagedEntry.view {dev := s.1.dev}
  (static.1, (fun pid => (s.2 pid).map (fun p => (p.internalId,p.staged))),
    static.2.2.1,static.2.2.2.1,static.2.2.2.2.1,
    (fun pid => ((s.2 pid).map (fun p => p.txQueue.all)).getD []))

theorem borrow_factor (w : WGWorld) : fromBorrow (PeerBorrow.view w) = StagedEntry.view w := by
  unfold fromBorrow StagedEntry.view
  apply Prod.ext
  · cases device : w.dev <;> simp [PeerBorrow.view,PeerBorrow.outsidePeers,wgStoreView,Packets.epoch,device]
  apply Prod.ext
  · funext pid
    cases device : w.dev <;> simp [PeerBorrow.view,PeerBorrow.resident,wgStoreView,Staged.stagedAt,device]
  apply Prod.ext
  · funext id
    cases device : w.dev <;> simp [PeerBorrow.view,PeerBorrow.outsidePeers,wgStoreView,
      PacketMaterial.view,TxDisposition.txPackets,device]
  apply Prod.ext
  · cases device : w.dev <;> simp [PeerBorrow.view,PeerBorrow.outsidePeers,wgStoreView,
      Packets.snapshot,Packets.deviceStore,device]
  apply Prod.ext
  · funext id
    cases device : w.dev <;> simp [PeerBorrow.view,PeerBorrow.outsidePeers,wgStoreView,TxDisposition.txPackets,device]
  · funext pid
    cases device : w.dev <;> simp [PeerBorrow.view,PeerBorrow.resident,wgStoreView,txQueueContents,handoffTxView,device]

theorem frame (pid : PeerId) : SameView StagedEntry.view (expiredZeroKeyMaterial pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  unfold expiredZeroKeyMaterial at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,ar,getter,alive,test,aTest,guard,tail⟩ := run
  obtain ⟨sameRead,sameAmbient,d,device,stored⟩ := getPeer_normal pid w read p a ar getter
  subst read
  subst ar
  have same := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (fun g => g=w) .zeroKeyAlive (!p.isDead))
    w a alive test aTest rfl guard
  have sameTest := same.2
  subst test
  cases alive with
  | false => simp only [Bool.false_eq_true,ite_false] at tail; cases tail; rfl
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨u,got,ag,acquire,dev,readDev,ad,getter,peek,peeked,ap,peeking,
      pending,checked,ac,guard,tail⟩ := tail
    cases u
    have borrowed := (hoare_iff_run_ambient _ _ _).mp
      (PeerBorrow.strict_acquire_spec pid (wgStoreView w)) w aTest () got ag rfl acquire
    have points := (ProjectedAction.iff_run_ambient _ _ _).mp (Queued.acquire pid) w aTest () got ag acquire
    have same := (DecryptCarrier.getDev_current ag ad getter).1
    subst readDev
    have same := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.peekQueuedUnit .clearPeerWorker pid) (fun g => g=got))
      got ad peek peeked ap rfl peeking
    subst peeked
    have same := (hoare_iff_run_ambient _ _ _).mp
      (branch_predicate_native (fun g => g=got) .zeroKeyAlreadyQueued
        (dev.clearWorkQueue.contains pid && !peek)) got ap pending checked ac rfl guard
    have sameWorld := same.2
    subst checked
    cases pending with
    | true =>
      simp only [ite_true] at tail
      have restored := (hoare_iff_run_ambient _ _ _).mp
        (PeerBorrow.repay_spec (some pid) (wgStoreView w)) got ac () v b borrowed tail
      exact (borrow_factor v).symm.trans ((congrArg fromBorrow restored).trans (borrow_factor w))
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨u,recorded,ar,record,install⟩ := tail
      have same := (hoare_iff_run_ambient _ _ _).mp
        (hoare_liftAmbient (AmbientM.recordQueued .clearPeerWorker pid) (fun g => g=got))
        got ac u recorded ar rfl record
      subst recorded
      have final := (ProjectedAction.iff_run_ambient _ _ _).mp
        (ReceiveFrames.device (fun e => {e with clearWorkQueue := e.clearWorkQueue ++ [pid]})
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) got ar () v b install
      exact final.trans points

theorem checked (pid : PeerId) (Safe : List Event → Prop)
    (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h) :
    SourcePassive.Checked debts locals Safe (Driver.timerObserved CausalJournal.hooks pid .zeroKeyMaterial) :=
  SourcePassive.native Safe entrySafe _ (frame pid)

/-- All five actual timer callbacks retain local entry accounting. Only
the independently implemented staging callback is an input contract. -/
theorem callback (pid : PeerId) (timer : PeerTimer) (Safe : List Event → Prop)
    (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
    (staging : SourcePassive.Checked debts locals Safe (Driver.stagingObserved CausalJournal.hooks pid)) :
    SourcePassive.Checked debts locals Safe (Driver.timerObserved CausalJournal.hooks pid timer) := by
  cases timer with
  | retransmitHandshake => exact TimerCallbacks.retransmit Safe entrySafe pid
  | sendKeepalive => exact TimerCallbacks.send_keepalive Safe entrySafe pid staging
  | newHandshake => exact TimerCallbacks.new_handshake Safe entrySafe pid
  | zeroKeyMaterial => exact checked pid Safe entrySafe
  | persistentKeepalive => exact TimerCallbacks.persistent Safe entrySafe pid staging

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ZeroTimer
