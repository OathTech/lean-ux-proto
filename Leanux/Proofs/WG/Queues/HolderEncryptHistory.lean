import Leanux.Proofs.WG.Queues.HolderEncryptFrames
import Leanux.Proofs.WG.Queues.HolderTxPublication

/-! The original encrypt iteration consumes its ring before actual NAPI, then
retains the returned account through encryption/publication and rescheduling. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderEncrypt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

theorem product_boundary {action : Leanux.M α} (ha : SameView productFields action) :
    Preserves (fun w : World => Boundary cs loans w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  exact boundary_fields hi ((ProjectedAction.iff_run _ _ _).mp ha w x v run)

theorem product_store_boundary {action : Leanux.M α} (ha : SameProductStore action) :
    Preserves (fun w : World => Boundary cs loans w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  have same := (ProjectedAction.iff_run _ _ _).mp ha w x v run
  have wg : wgStoreView v.wg = wgStoreView w.wg := congrArg (fun p : ProductStore43 => p.2.2.2) same
  obtain ⟨holders,funded,stable⟩ := hi
  exact ⟨holders,⟨funded.aligned.frame (Frame.of_store wg),funded.carriers.kernel wg⟩,stable.kernel wg⟩

theorem packet_boundary (kid : KeypairId) (pkt : DataPacket) :
    Preserves (fun w : World => Boundary cs loans w.wg) (encryptPacket Env.checksumHelp kid pkt) :=
  product_boundary (encryptPacket_fields Env.checksumHelp
    (fun p => (checksumHelp_sameWorld p).factor productFields) kid pkt)

theorem step_tail_boundary (item : Option (List SkbId)) :
    Preserves (fun w : World => Boundary cs loans w.wg) (RxWorkers.encryptStepTailSource item) := by
  let P := fun w : World => Boundary cs loans w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (liftAmbient a) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  have getter := fun id => lift_boundary (cs := cs) (loans := loans) (native_boundary (getTx_fields id))
  have setter := fun id f => lift_boundary (cs := cs) (loans := loans) (native_boundary (setTx_fields id f))
  have publish := fun item state => lift_boundary (cs := cs) (loans := loans) (enqueuePerPeerTx_boundary item state)
  change Preserves P _
  unfold RxWorkers.encryptStepTailSource
  apply preserves_bind (ambient (AmbientM.branch .encWorkerConsumed item.isSome))
  intro _
  cases item with
  | none => exact preserves_pure _
  | some first =>
    dsimp only
    cases hh : first.head? with
    | none => exact ambient (AmbientM.invariant _)
    | some headId =>
      dsimp only
      apply preserves_bind (getter headId)
      intro head
      apply preserves_bind
      · apply list_view_spec id P
        intro id state
        apply preserves_bind (ambient (AmbientM.branch .encWorkerSkbIterate true))
        intro _
        apply preserves_bind (getter id)
        intro packet
        apply preserves_bind (packet_boundary head.keypair packet)
        intro encrypted
        apply preserves_bind (ambient (AmbientM.branch .encWorkerEncrypted encrypted.isSome))
        intro success
        split
        · exact preserves_bind (setter id _) (fun _ => preserves_pure _)
        · exact preserves_pure _
      · intro state
        split
        · exact preserves_bind (ambient (AmbientM.branch .encWorkerSkbIterate false))
            (fun _ => preserves_bind (publish first state) (fun _ => preserves_pure _))
        · exact preserves_bind (publish first state) (fun _ => preserves_pure _)


theorem tail_boundary (item : Option (List SkbId)) :
    Preserves (fun w : World => Boundary cs loans w.wg) (RxWorkers.encryptTailSource item) := by
  unfold RxWorkers.encryptTailSource workerIter
  apply preserves_bind (step_tail_boundary item)
  intro more
  split
  · exact preserves_pure _
  · apply preserves_bind
    · apply preserves_bind (product_store_boundary (condResched_sameKernel .encryptWorker))
      intro need
      exact productAmbient_spec (AmbientM.branch .encWorkerNeedResched need) _ (fun _ _ hi => hi)
    · intro yielded
      split <;> exact preserves_pure _

/-- Audit-only source cuts append no RX removal event, while retaining their
actual full product action and the exact incoming journal. -/
theorem mixed_at (action : PrefixM LifetimeEvent α) (original : Leanux.M α)
    (erases : ErasesPrefix action original)
    (keeps : ∀ cs, Preserves (fun w : World => Boundary cs loans w.wg) original)
    (hi : HolderNapi.At initial loans before h w)
    (run : runPrefix (RxHistory.mixed action) w h = (.ok (x,v),k)) :
    HolderNapi.At initial loans before k v := by
  obtain ⟨old,history,stable⟩ := hi
  have native : original.run w = .ok (x,v) :=
    (RxHistory.mixed_erases erases w h).symm.trans (congrArg Prod.fst run)
  apply HolderDecryptHistory.quiet_cut (Appends.focus _ _ _) _ history run
    ((hoare_iff_run _ _ _).mp (keeps _) w x v stable native)
  intro w h
  exact focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent NapiCarrier.removed
    (fun _ => rfl) (auditFocus action) w h

theorem iteration_normal (hi : HolderNapi.At initial loans before h w)
    (run : runPrefix RxHistory.encryptIteration w h = (.ok (result,v),k)) :
    HolderNapi.At initial loans before k v := by
  unfold RxHistory.encryptIteration at run
  obtain ⟨item,polled,polledHistory,pollRun,rest⟩ := DecryptIteration.bind_normal run
  have first := mixed_at _ _ (liftWGObserver_erases (erasesStatePrefix_lift TxRing.pollSource))
    (fun _ => lift_boundary (native_boundary poll_fields)) hi pollRun
  obtain ⟨u,received,receivedHistory,napiRun,tailRun⟩ := DecryptIteration.bind_normal rest
  cases u
  have middle := HolderDecryptHistory.softirq_at first napiRun
  exact mixed_at _ _ (RxWorkers.encryptTail_erases item) (fun _ => tail_boundary item) middle tailRun

theorem native_normal (hi : Boundary cs loans w.wg)
    (run : (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)).run w = .ok (result,v))
    (h : List RxHistory.Event) :
    let k := (runPrefix RxHistory.encryptIteration w h).2
    ∃ suffix, k = h ++ suffix ∧ Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg := by
  have observed : runPrefix RxHistory.encryptIteration w h =
      (.ok (result,v),(runPrefix RxHistory.encryptIteration w h).2) :=
    Prod.ext ((RxHistory.encryptIteration_erases w h).trans run) rfl
  exact iteration_normal (HolderNapi.at_start hi h) observed


theorem physical_normal (physical : DecryptIteration.Physical w)
    (run : (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)).run w = .ok (result,v)) :
    DecryptIteration.Physical v := by
  obtain ⟨epoch,n,history,ring,refines,cell⟩ := physical
  have same := (ProjectedAction.iff_run _ _ _).mp RxRing.actualEncryptIter_cell w result v run
  exact ⟨epoch,n,history,ring,refines,same.trans cell⟩

/-- Account and physical RX ring remain tied to this same actual iteration. -/
theorem native_funded (hi : Boundary cs loans w.wg) (physical : DecryptIteration.Physical w)
    (run : (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)).run w = .ok (result,v))
    (h : List RxHistory.Event) :
    let k := (runPrefix RxHistory.encryptIteration w h).2
    (∃ suffix, k = h ++ suffix ∧ Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧
      DecryptIteration.Physical v :=
  ⟨native_normal hi run h,physical_normal physical run⟩

end Leanux.Proofs.WG.Queues.RxCredits.HolderEncrypt
