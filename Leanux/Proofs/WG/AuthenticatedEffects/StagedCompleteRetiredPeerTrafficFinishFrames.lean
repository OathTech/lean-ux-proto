import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTrafficSections

/-! Actual deferred traffic tails preserve the same exact account. Only
inject's original drain guard supplies an empty RX ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Traffic
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders

theorem inject_finish (actors : Scheduler.Actors initial loans before) (hi : Auxiliary.Inv initial loans before h w)
    (run : runPrefix (InjectAccount.finish msg) w h=(.ok (result,v),k)) :
    ∃ u j suffix, runPrefix RxHistory.runCryptWorkers w h=(.ok ((),u),j) ∧
      j=before++suffix ∧ remaining initial (NapiCarrier.removedPackets suffix)=[] ∧
      Auxiliary.Inv [] loans k k v ∧ result=(msg.length : Int) ∧
      (∀ (d : Device) (id : SkbId) (packet : RxPacket), v.wg.dev=some d → d.rxSkbs[id]?≠some packet) := by
  unfold InjectAccount.finish at run
  obtain ⟨x,u,j,crypt,tail⟩ := DecryptIteration.bind_normal run
  cases x
  have after := (Deferred.crypt actors w h hi).choose_spec.2.2
  rw [crypt] at after
  have read : (liftWG getDev).run u =
      match u.wg.dev with
      | none => .error (.invariant "no WireGuard device in this trace's fixture")
      | some d => .ok (d,u) := by
    exact (pinned_const _private.Leanux.Proofs.WG.Queues.RxDrainBoundary.«0».Leanux.Proofs.WG.Queues.RxCredits.readDev) u
  rw [runPrefix_bind,runPrefix_lift,read] at tail
  cases hd : u.wg.dev with
  | none => simp only [hd] at tail; cases tail
  | some d =>
    simp only [hd] at tail
    obtain ⟨x,t,l,drain,done⟩ := DecryptIteration.bind_normal tail
    cases x
    simp only [runPrefix_pure,Prod.mk.injEq,Except.ok.injEq] at done
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := done
    have membership : ∀ d',u.wg.dev=some d' → (!d'.decryptQueue.empty)∈
        [!d.handshakeQueue.empty,!d.decryptQueue.empty,!d.encryptQueue.empty,!d.txWorkQueue.isEmpty] := by
      intro d' eq
      have same := hd.symm.trans eq
      cases same
      exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    obtain ⟨suffix,hist,empty,noPackets,post⟩ := Deferred.drained_empty after membership drain
    have actual := (RxHistory.mixed_erases (requireDrainedPrefix_erases _ _) u j).symm.trans (congrArg Prod.fst drain)
    have same := (requireDrained_normal _ _ u t actual).1
    have account : ExactBoundary [] loans u.wg := by
      simpa only [empty] using after.residual hist
    have finalAccount : ExactBoundary [] loans t.wg := by simpa only [same] using account

    exact ⟨u,j,suffix,crypt,hist,empty,
      ⟨HolderInitial.at_cut finalAccount.lower post.1.1.2 post.1.2.1 post.1.2.2,
        ExactAt.start finalAccount l⟩,rfl,noPackets⟩


theorem flood_finish (actors : Scheduler.Actors initial loans before) :
    PrefixPreserves (Auxiliary.Inv initial loans before) OwnerChecks.Safe FloodAccount.finish := by
  have safe : ∀ h w,Auxiliary.Inv initial loans before h w→OwnerChecks.Safe h := fun _ _ hi=>hi.safe
  have store : ∀ h w v,productStoreView v=productStoreView w→Auxiliary.Inv initial loans before h w→Auxiliary.Inv initial loans before h v := fun _ _ _ same hi=>Auxiliary.store hi same
  unfold FloodAccount.finish
  apply PrefixPreserves.bind (after_batch actors)
  intro x
  repeat' first
    | exact Deferred.drained _ _
    | traffic_preserve_source safe using store

theorem batch_finish (actors : Scheduler.Actors initial loans before)
    (entries : List Env.BatchItem) (cqes : List Int) :
    PrefixPreserves (Auxiliary.Inv initial loans before) OwnerChecks.Safe (BatchAccount.finish entries cqes) := by
  have safe : ∀ h w,Auxiliary.Inv initial loans before h w→OwnerChecks.Safe h := fun _ _ hi=>hi.safe
  have store : ∀ h w v,productStoreView v=productStoreView w→Auxiliary.Inv initial loans before h w→Auxiliary.Inv initial loans before h v := fun _ _ _ same hi=>Auxiliary.store hi same
  unfold BatchAccount.finish
  repeat' first
    | (traffic_head RxHistory.afterBatch; exact after_batch actors)
    | traffic_preserve_source safe using store

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Traffic
