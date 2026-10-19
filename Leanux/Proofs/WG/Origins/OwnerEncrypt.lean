import Leanux.Proofs.WG.Origins.OwnerWorkers

/-! The existing encrypt observer preserves receiving-owner checks. Packet
adapters require the actual RX-store frame; arbitrary SkbM writes are excluded. -/
namespace Leanux.Proofs.WG.OwnerEncrypt
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Queues.RxCredits OwnerBounds
open Origins.HistorySupport (sensitive)

private theorem skb {α : Type} (a : SkbM α)
    (rx : SameView rxView (liftSkb a)) : Preserves Carrier (liftSkb a) := by
  apply OwnerCompletion.preserves_of_frames (allowed := NoPromotion) _
  · apply Origins.Retaining.of_view
    intro initial
    apply hoare_liftSkb
    intro w d packets hi hd
    simpa only [Origins.view,id_eq,hd,Option.map_some] using hi
  · exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.skb) a rx
  · apply keyEffects_view (project := id)
    intro initial
    apply hoare_liftSkb
    intro w d packets hi hd
    unfold keyView keyWords currentCells at hi ⊢
    simpa only [id_eq,hd,Option.map_some,Option.bind_some] using hi

private theorem product_store (a : Leanux.M α) (frame : SameProductStore a) :
    Preserves (fun w : World => Carrier w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi hr
  exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_sameDev)
    hi (congrArg (fun s : ProductStore43 => s.2.2.2.dev)
      ((ProjectedAction.iff_run _ _ _).mp frame w result v hr))

private theorem encrypt (key : KeypairId) (pkt : DataPacket) :
    Preserves (fun w : World => Carrier w.wg) (encryptPacket Env.checksumHelp key pkt) := by
  let P := fun w : World => Carrier w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerPoll.«0».Leanux.Proofs.WG.OwnerPoll.native_product)
      _ ((calculateSkbPadding_sameWGWorld _ _).wp Carrier)
  have checksumSpec (p : WG.Packet) : Preserves P (Env.checksumHelp p) := (checksumHelp_sameWorld p).wp P
  have keySpec : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) := by
    apply (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerPoll.«0».Leanux.Proofs.WG.OwnerPoll.native_product)
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a k v b hi hr
    exact (KeyTimes.getKeypair_return key w v k a b hr).1 ▸ hi
  routing_tx_source [encryptPacket] using [padding,checksumSpec,keySpec,ambient]

private theorem enqueue (xs : List SkbId) (state : PacketState) :
    Preserves Carrier (enqueuePerPeerTx xs state) :=
  OwnerCompletion.preserves_of_frames _ (Origins.Retaining.enqueuePerPeerTx_material xs state)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.enqueuePeer_geometry) xs state)
    (publication_keyEffect (allowed := NoPromotion) xs state)

theorem encryptTail_preserves (item : Option (List SkbId)) :
    Preserves (fun w : World => Carrier w.wg) (RxWorkers.encryptTailSource item) := by
  let P := fun w : World => Carrier w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerPoll.«0».Leanux.Proofs.WG.OwnerPoll.native_product)
      _ (skb _ ((getTx_protect id).of_factor (fun v => v.2.1) _ (fun _ => rfl)))
  have write (id : SkbId) (f : DataPacket → DataPacket) :
      Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerPoll.«0».Leanux.Proofs.WG.OwnerPoll.native_product)
      _ (skb _ ((setTx_protect id f).of_factor (fun v => v.2.1) _ (fun _ => rfl)))
  have publish (xs : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerPoll.«0».Leanux.Proofs.WG.OwnerPoll.native_product)
      _ (enqueue xs state)
  have packet (key : KeypairId) (pkt : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key pkt) := encrypt key pkt
  have stepSpec : Preserves P (RxWorkers.encryptStepTailSource item) := by
    routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,packet,publish,ambient]
  have needSpec : Preserves P (Env.condResched .encryptWorker) :=
    product_store _ (condResched_sameKernel _)
  routing_tx_source [RxWorkers.encryptTailSource,workerIter] using [stepSpec,needSpec,ambient]

private theorem poll :
    OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver (liftWGPrefix TxRing.pollSource))) := by
  apply OwnerChecks.native_quiet _ TxRing.pollSource (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift _)))
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
      sensitive (fun _ => rfl) _)
  · apply (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.native_mixed)
      _ _ (erasesStatePrefix_lift _)
    · exact Origins.Retaining.of_view
        (pinned_const _private.Leanux.Proofs.WG.Origins.RetainingTraffic.«0».Leanux.Proofs.WG.Origins.Retaining.encryptPoll_material)
    · intro history
      unfold TxRing.pollSource
      repeat' current_lifecycle_step history
  · exact RxHistory.mixed_preserves
      (pinned_const _private.Leanux.Proofs.WG.Queues.RxWorkerHistory.«0».Leanux.Proofs.WG.Queues.RxHistory.encryptPoll_allocation)
  · intro history
    apply hoare_consequence (show Preserves Carrier TxRing.pollSource from by
      unfold TxRing.pollSource
      repeat' owner_control_step)
      (fun _ hi => hi.2) (fun _ _ hi => hi)

private theorem tail (item : Option (List SkbId)) :
    OwnerChecks.Preserves (RxHistory.mixed (RxWorkers.encryptTail item)) := by
  apply OwnerChecks.quiet _ (Appends.focus _ _ _)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
      sensitive (fun _ => rfl) _)
  · exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.mixed)
      _ _ (RxWorkers.encryptTail_erases item)
      ((pinned_const _private.Leanux.Proofs.WG.Origins.SupportCallers.«0».Leanux.Proofs.WG.Origins.HistorySupport.encryptTail_material) item)
      ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.encryptTail_preserves) item)
  · exact RxHistory.mixed_preserves (RxWorkers.encryptTail_preserves item)
  · intro w h hi result v hr
    exact (hoare_iff_run _ _ _).mp (encryptTail_preserves item) w result v hi.carrier
      ((RxHistory.mixed_erases (RxWorkers.encryptTail_erases item) w h).symm.trans hr)

theorem encryptIteration : OwnerChecks.Preserves RxHistory.encryptIteration := by
  unfold RxHistory.encryptIteration
  exact poll.bind (fun item => OwnerWorkers.napiSoftirq.bind (fun _ => tail item))

end Leanux.Proofs.WG.OwnerEncrypt
