import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerBaseFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerNativeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDrain

/-! Native removal preserves the exact remaining holder account and pays the
source-selected detached occurrences after the actual work drains. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

namespace Removal

theorem fields {action : WG.M α} (same : SameView HolderEncrypt.fields action) :
    Preserves (DuringWork original carriers loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b before run
  obtain ⟨holders,remainder,account⟩ := before
  exact ⟨holders,remainder,account.fields
    ((ProjectedAction.iff_run_ambient _ _ _).mp same w a x v b run)⟩

theorem decrement : Preserves (DuringWork original carriers loans)
    (modifyDev fun d => {d with numPeers := d.numPeers - 1}) := by
  apply hoare_modify
  rintro w ⟨holders,remainder,account⟩
  refine ⟨holders,remainder,account.fields ?_⟩
  cases w with
  | mk dev => cases dev <;> rfl

theorem prepare (pid : PeerId) :
    Preserves (DuringWork original carriers loans) (RetirementSecurity.HolderRemoval.preparation pid) := by
  unfold RetirementSecurity.HolderRemoval.preparation
  index_unfold _private.Leanux.Proofs.WG.Queues.HolderRetirement.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.beforePayment
  repeat' first
    | (rx_retention_head getPeer
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a p v b before run
       exact (getPeer_normal _ w v p a b run).1 ▸ before)
    | (rx_retention_head getDev
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a d v b before run
       exact (DecryptCarrier.getDev_current a b run).1 ▸ before)
    | (rx_retention_head keypairsClear; exact keypairsClear_preserves _)
    | (rx_retention_head timersStop; exact timersStop_preserves _)
    | (rx_retention_head drainHandshakeSendWq; exact drain_preserves _ _ _ _)
    | (rx_retention_head modifyDev; exact decrement)
    | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (rx_retention_head unsupported; exact hoare_liftAmbient (AmbientM.unsupported _) _)
    | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
    | rxstack_preserves_join
    | rx_retention_step

theorem payment (before : DuringWork original carriers (owner :: loans) w)
    (run : ((peerPut (some owner.slot)).run w).run a = .ok (((),v),b)) :
    DuringWork original carriers loans v := by
  obtain ⟨holders,remainder,account⟩ := before
  exact ⟨holders,remainder,account.payment run⟩

theorem after_dead (before : DuringWork original carriers (owner :: loans) w) (a b : Ambient)
    (run : ((peerRemoveAfterDead owner.slot).run w).run a = .ok (((),v),b)) :
    DuringWork original carriers loans v := by
  rw [(pinned_const _private.Leanux.Proofs.WG.Queues.HolderRetirement.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.afterDead_factor),
    MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ignored,u,c,prefixRun,paid⟩ := run
  cases ignored
  exact payment ((hoare_iff_run_ambient _ _ _).mp (prepare owner.slot)
    w a () u c before prefixRun) paid

theorem some_peer (account : Account holders carriers loans w) (pid : PeerId)
    (unique : (holders.base.map Owner.slot).Nodup)
    (selected : pid ∈ holders.base.map Owner.slot) (a b : Ambient)
    (run : ((peerRemove (some pid)).run w).run a = .ok (((),v),b)) :
    DuringWork (holders.withoutBase (BaseRemoval.live holders.base pid)) carriers loans v := by
  obtain ⟨owner,slot,one⟩ := unique_detached holders.base pid unique selected
  change ((peerMakeDead pid >>= fun _ => peerRemoveAfterDead pid).run w).run
    (CounterWindow.record a .peerRemoveNull false) = .ok (((),v),b) at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ignored,marked,c,mark,paid⟩ := run
  cases ignored
  have markedAccount := account.make_dead pid mark
  rw [one,List.singleton_append] at markedAccount
  exact after_dead (duringWork_initial markedAccount) c b (by simpa only [slot] using paid)

theorem saved_after_dead (saved : Reservations)
    (before : DuringWork original carriers (saved ++ loans) w) (a b : Ambient)
    (run : (((for pid in saved.map Owner.slot do
      _ ← branch .peerRemoveAllIter2 true
      peerRemoveAfterDead pid) : WG.M Unit).run w).run a = .ok (((),v),b)) :
    DuringWork original carriers loans v := by
  induction saved generalizing w a with
  | nil =>
    simp only [List.map_nil,List.forIn_nil] at run
    cases run
    exact before
  | cons o saved ih =>
    have factor : (for pid in (o :: saved).map Owner.slot do
        _ ← branch .peerRemoveAllIter2 true
        peerRemoveAfterDead pid : WG.M Unit) = (do
        _ ← branch .peerRemoveAllIter2 true
        peerRemoveAfterDead o.slot
        for pid in saved.map Owner.slot do
          _ ← branch .peerRemoveAllIter2 true
          peerRemoveAfterDead pid) := by
      simp only [List.map_cons,List.forIn_cons,bind_assoc,pure_bind]
    rw [factor,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨flag,read,c,decision,rest⟩ := run
    have same := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter2 true) (fun g => g=w))
      w a flag read c rfl decision
    subst read
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨ignored,paid,d,payment,rest⟩ := rest
    cases ignored
    exact ih (after_dead before c d payment) d rest

theorem all_peers (account : Account holders carriers loans w) (a b : Ambient)
    (run : (peerRemoveAll.run w).run a = .ok (((),v),b)) :
    DuringWork (holders.withoutBase []) carriers loans v := by
  rw [BaseRemoval.peerRemoveAll_entry,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨dead,entered,c,entry,rest⟩ := run
  obtain ⟨saved,enteredAccount⟩ := account.saved_entry a c entry
  subst dead
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨ignored,marked,d,mark,rest⟩ := rest
  cases ignored
  have markedReady := duringWork_initial (enteredAccount.saved_make_dead (v := marked) c d (by
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨PUnit.unit,marked,d,mark,rfl⟩))
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨flag,read,e,decision,rest⟩ := rest
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter1 false) (fun g => g=marked))
    marked d flag read e rfl decision
  subst read
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨ignored,paid,f,payment,rest⟩ := rest
  cases ignored
  have done := saved_after_dead (v := paid) holders.base markedReady e f (by
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨PUnit.unit,paid,f,payment,rfl⟩)
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨last,read,g,decision,rest⟩ := rest
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter2 false) (fun state => state=paid))
    paid f last read g rfl decision
  subst read
  cases rest
  exact done

end Removal
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
