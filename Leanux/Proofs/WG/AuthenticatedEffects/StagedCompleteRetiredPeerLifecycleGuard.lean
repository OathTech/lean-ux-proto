import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecycleStop
import Leanux.Proofs.WG.RetirementSecurity.TxDestructSource

/-! The actual destructor preparation removes the live base while retaining
one exact account for all surviving work, carriers and loans. Its checked cut
is exposed before reset; no absence of queued or staged objects is assumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders
set_option maxHeartbeats 600000

/-- The remaining holder witness is shared by the funded lower bound, exact
upper bound and empty-base fact. The native cursors are also inactive. -/
def EmptyBase (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  ∃holders, Account holders cs loans w ∧ holders.base=[] ∧
    activeCursor w.nlSock7=none ∧ activeCursor w.nlSock8=none

theorem EmptyBase.clear (before : EmptyBase cs loans w) : Clear cs loans w := by
  obtain ⟨h,account,_,c7,c8⟩ := before
  exact ⟨⟨h,account⟩,c7,c8⟩

theorem EmptyBase.native_base (before : EmptyBase cs loans w) :
    (w.dev.map Device.peerList).getD []=[] := by
  obtain ⟨h,account,empty,_,_⟩ := before
  simpa [empty] using account.funded.aligned.base.symm

theorem remove_all : Hoare peerRemoveAll (Clear cs loans) (fun _=>EmptyBase cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b before run
  cases x
  obtain ⟨⟨h,account⟩,c7,c8⟩ := before
  obtain ⟨out,rest,post⟩ := Removal.all_peers account a b run
  refine ⟨out,post,rest.base,?_,?_⟩
  · rw [←post.funded.aligned.cursor7,rest.cursor7]
    exact account.funded.aligned.cursor7.trans c7
  · rw [←post.funded.aligned.cursor8,rest.cursor8]
    exact account.funded.aligned.cursor8.trans c8

theorem prepare : Hoare RetirementSecurity.TxWork.Destruct.prepare
    (Clear cs loans) (fun _=>EmptyBase cs loans) := by
  unfold RetirementSecurity.TxWork.Destruct.prepare
  apply hoare_bind _ _ (show Preserves (Clear cs loans)
    (modifyDev fun d=>{d with creatingNet:=false,incomingPort:=0}) from ?_)
  · intro _
    apply hoare_bind _ _ (clear_socket none none)
    intro _
    exact remove_all
  · apply clear_modify
    intro w
    unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
    unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
    cases hd:w.dev <;> simp [hd,rxView]

theorem empty_store (action : WG.M α) (frame : SameWGStore action) :
    Preserves (EmptyBase cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b before run
  obtain ⟨h,account,empty,c7,c8⟩ := before
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp frame w a x v b run
  exact ⟨h,account.store same,empty,
    (congrArg (fun s : WGStoreView=>activeCursor s.nlSock7) same).trans c7,
    (congrArg (fun s : WGStoreView=>activeCursor s.nlSock8) same).trans c8⟩

theorem check : Preserves (EmptyBase cs loans) RetirementSecurity.TxWork.Destruct.check := by
  unfold RetirementSecurity.TxWork.Destruct.check
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head getDev; exact empty_store _ getDev_sameWGStore)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (EmptyBase cs loans))
    | rx_retention_step

private theorem limiter : Preserves (EmptyBase cs loans) ratelimiterUninit := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b before run
  obtain ⟨h,account,base,c7,c8⟩ := before
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp ratelimiterUninit_sameRatelimiter w a x v b run
  exact ⟨h,account.fields (congrArg
    (fun s : WGStoreView=>HolderEncrypt.fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8}) same),base,
    (congrArg (fun s : WGStoreView=>activeCursor s.nlSock7) same).trans c7,
    (congrArg (fun s : WGStoreView=>activeCursor s.nlSock8) same).trans c8⟩

theorem settle : Preserves (EmptyBase cs loans) RetirementSecurity.TxWork.Destruct.settle := by
  unfold RetirementSecurity.TxWork.Destruct.settle
  repeat' first
    | (rx_retention_head mayHaveSlept; exact empty_store _ mayHaveSlept_sameWGStore)
    | (rx_retention_head ratelimiterUninit; exact limiter)
    | (rx_retention_head modifyDev
       apply hoare_modify
       rintro w ⟨h,account,base,c7,c8⟩
       refine ⟨h,account.fields ?_,base,c7,c8⟩
       cases w with | mk dev => cases dev <;> rfl)
    | rx_retention_step

theorem before_reset : Hoare RetirementSecurity.TxWork.Destruct.beforeReset
    (Clear cs loans) (fun _=>EmptyBase cs loans) := by
  unfold RetirementSecurity.TxWork.Destruct.beforeReset
  apply hoare_bind _ _ prepare
  intro _
  exact preserves_bind check (fun _=>settle)

/-- Successful native destruction exposes the actual prepared guard entry
and checked pre-reset state, with one exact surviving account at both cuts. -/
theorem destruct_cuts (before : Clear cs loans w)
    (run : (wgDestruct.run w).run a=.ok (((),v),b)) :
    ∃u c z e,
      (RetirementSecurity.TxWork.Destruct.prepare.run w).run a=.ok (((),u),c) ∧
      EmptyBase cs loans u ∧
      ((do RetirementSecurity.TxWork.Destruct.check
           RetirementSecurity.TxWork.Destruct.settle : WG.M Unit).run u).run c=.ok (((),z),e) ∧
      EmptyBase cs loans z ∧
      ((do _root_.modify fun g:WGWorld=>{g with dev:=none}
           retireDeviceUnits : WG.M Unit).run z).run e=.ok (((),v),b) := by
  rw [RetirementSecurity.TxWork.Destruct.factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨result,z,e,preparedPrefix,reset⟩ := run
  cases result
  have atReset := (hoare_iff_run_ambient _ _ _).mp before_reset w a () z e before preparedPrefix
  change (((RetirementSecurity.TxWork.Destruct.prepare >>= fun _=>do
    RetirementSecurity.TxWork.Destruct.check
    RetirementSecurity.TxWork.Destruct.settle).run w).run a)=.ok (((),z),e) at preparedPrefix
  rw [MaterialOrigin.bind_ok_ambient] at preparedPrefix
  obtain ⟨ignored,u,c,prepared,tail⟩ := preparedPrefix
  cases ignored
  exact ⟨u,c,z,e,prepared,(hoare_iff_run_ambient _ _ _).mp prepare w a () u c before prepared,
    tail,atReset,reset⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle
