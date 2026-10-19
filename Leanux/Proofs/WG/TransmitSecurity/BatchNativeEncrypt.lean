import Leanux.Proofs.WG.TransmitSecurity.BatchNativeDecrypt

/-! The native encrypt worker edits only bytes and publication state. It
keeps queued batch alignment while its polled alias is held across NAPI. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Encrypt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open RetirementSecurity Queues.RxCredits Native Stack

theorem tail_inv (items : Option (List SkbId)) :
    Preserves (fun w : World => Inv w.wg)
      (RxWorkers.encryptStepTailSource items) := by
  let Q := fun w : WGWorld => Inv w
  let P := fun w : World => Q w.wg
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : Leanux.M α) :=
    productAmbient_spec action P (fun _ _ hi => hi)
  have readNative (id : SkbId) : Preserves Q (getTxSkb id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b before run
    exact (Packets.getTxSkb_current id w v p a b run).1 ▸ before
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    PublicationPoll.native_product Q _ (readNative id)
  have writeNative (id : SkbId) (bytes : List UInt8) :
      Preserves Q (setTxSkb id (fun p => {p with bytes})) :=
    Native.write_packet id _ (fun _ => rfl)
  have write (id : SkbId) (bytes : List UInt8) :
      Preserves P (monadLift (setTxSkb id (fun p => {p with bytes})) : Leanux.M Unit) :=
    PublicationPoll.native_product Q _ (writeNative id bytes)
  have publishNative (batch : List SkbId) (state : PacketState) :
      Preserves Q (enqueuePerPeerTx batch state) := Native.publish batch state
  have publish (batch : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx batch state) : Leanux.M Unit) :=
    PublicationPoll.native_product Q _ (publishNative batch state)
  have packet (key : KeypairId) (pkt : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key pkt) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    have same := (ProjectedAction.iff_run _ _ _).mp (encrypt_packet_store key pkt) w result v run
    have dev : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev same
    apply before.frame
    dsimp only [view]
    apply Prod.ext
    · funext pid; simp only [handoffTxView,dev]
    · funext id; simp only [PacketMaterial.view,TxDisposition.txPackets,dev]
  change Preserves P _
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,packet,publish,ambient]

theorem tail_inv_full (item : Option (List SkbId)) :
    Preserves (fun w : World => Inv w.wg) (RxWorkers.encryptTailSource item) := by
  let P := fun w : World => Inv w.wg
  have need : Preserves P (Env.condResched .encryptWorker) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    have same := congrArg (fun s : ProductStore43 => s.2.2.2.dev)
      ((ProjectedAction.iff_run _ _ _).mp (condResched_sameKernel _) w result v run)
    change v.wg.dev = w.wg.dev at same
    apply before.frame
    dsimp only [view]
    apply Prod.ext
    · funext pid; simp only [handoffTxView,same]
    · funext id; simp only [PacketMaterial.view,TxDisposition.txPackets,same]
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  have next := tail_inv item
  routing_tx_source [RxWorkers.encryptTailSource,workerIter] using [next,need,ambient]

theorem tail (before : Coherent locals (item.toList ++ active) w.wg)
    (run : (RxWorkers.encryptTailSource item).run w = .ok (result,v)) : Coherent locals active v.wg :=
  ⟨OccurrenceEncrypt.tail before.1 run,
    (hoare_iff_run _ _ _).mp (tail_inv_full item) w result v before.2 run⟩

theorem poll_inv : Preserves Inv TxRing.pollSource := by
  have read := Native.store getDev_sameWGStore
  have edit (queue : PtrRing (List SkbId)) : Preserves Inv (modifyDev fun d => {d with encryptQueue := queue}) :=
    Native.modify_device _ (fun _ => rfl) (fun _ => rfl)
  have ambient {α : Type} (a : AmbientM α) : Preserves Inv (monadLift a : WG.M α) := hoare_liftAmbient a Inv
  rxstack_preserves_source [TxRing.pollSource] using [read,edit,ambient]

theorem poll (before : Coherent locals active w) (a b : Ambient)
    (run : (TxRing.pollSource.run w).run a = .ok ((item,v),b)) :
    Coherent locals (item.toList ++ active) v :=
  ⟨OccurrenceEncrypt.poll before.1 a b run,
    (hoare_iff_run_ambient _ _ _).mp poll_inv w a item v b before.2 run⟩

theorem iteration : Preserves (fun w : World => Coherent locals active w.wg)
    (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  rw [RxWorkers.encrypt_source,MaterialOrigin.bind_ok] at run
  obtain ⟨item,u,pollRun,run⟩ := run
  have polled : Coherent locals (item.toList ++ active) u.wg := by
    rw [liftWG_run] at pollRun
    cases native : (TxRing.pollSource.run w.wg).run w.ambient with
    | error e => simp [native,Except.map] at pollRun
    | ok output =>
      obtain ⟨⟨out,g⟩,a⟩ := output
      simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at pollRun
      obtain ⟨rfl,rfl⟩ := pollRun
      exact poll before w.ambient a native
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨_,t,callback,tailRun⟩ := run
  exact tail ((hoare_iff_run _ _ _).mp (Napi.softirq locals (item.toList ++ active))
    u () t polled callback) tailRun

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Encrypt
