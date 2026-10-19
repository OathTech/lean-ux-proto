import Leanux.Proofs.WG.Origins.CurrentReceiveChecks
import Leanux.Proofs.WG.Origins.CurrentSensitive
import Leanux.Proofs.WG.Origins.CurrentRx
import Leanux.Proofs.WG.Origins.CurrentPollHistory

/-! Current checks through the existing worker observers. Native publication
keeps its saved peer across the packet write. Decrypt receipts and incoming
histories retain their actual positional cuts, including failed prefixes. -/
namespace Leanux.Proofs.WG.CurrentWorkers
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues CurrentLifecycle CurrentTraffic ConfiguredHandshake
open Origins hiding Inv
open Origins.HistorySupport (sessions sensitive rxEncode rxDecode rx_decode_encode)

private theorem safe (h : List RxHistory.Event) (w : World) (hi : CurrentChecks.Inv h w) :
    CurrentChecks.Safe h := ⟨hi.1.1,hi.2.2⟩

private theorem store (h : List RxHistory.Event) (w v : World)
    (eq : productStoreView v = productStoreView w) (hi : CurrentChecks.Inv h w) :
    CurrentChecks.Inv h v := by
  have dev : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) eq
  refine ⟨hi.1.kernel eq,⟨?_,?_⟩,hi.2.2⟩
  · intro s hs
    exact hi.2.1.1 s (by simpa only [ConfiguredIdentity.view,dev] using hs)
  · intro d hd slot key hk valid
    exact hi.2.1.2 d (dev.symm.trans hd) slot key hk valid

private theorem native_store (a : WG.M α) (frame : SameView wgStoreView a)
    (history : List SessionOrigin.Receipt) : Preserves (Inv history) a :=
  current_preserves a (ConfiguredIdentity.sameWG (project := id) frame)
    (Retaining.of_view (Origins.sameView_of_sameWG (project := id) frame)) history

theorem publish_preserves (id : SkbId) (state : PacketState)
    (history : List SessionOrigin.Receipt) : Preserves (Inv history) (RxWorkers.publishSource id state) := by
  unfold RxWorkers.publishSource getRxSkb
  apply preserves_bind
    (show Preserves (Inv history) (liftSkb (SkbStore.getRx id)) from by current_skb_step history)
  intro pkt
  apply preserves_bind (indexOwner_peerDeref_preserves (.keypair pkt.keypair) (Inv history))
  intro pid
  apply preserves_bind (show Preserves (Inv history) (peerGet pid) from by current_traffic_step history)
  intro _
  apply hoare_bind _ _ (CurrentTraffic.readPeer_spec history pid)
  intro p
  let Q := fun w => Inv history w ∧
    (ConfiguredIdentity.view w).bind (fun s => s.peers pid) = some (ConfiguredIdentity.cell p)
  have write : Preserves Q (setRxSkb id fun q => {q with state}) := by
    unfold setRxSkb
    apply hoare_liftSkb
    intro w d packets hi hd
    rcases hi with ⟨⟨configured,current⟩,saved⟩
    refine ⟨⟨?_,?_⟩,?_⟩
    · simpa only [ConfiguredIdentity.Inv,ConfiguredIdentity.InvExcept,ConfiguredIdentity.view,
        hd,Option.map_some,ConfiguredIdentity.state] using configured
    · intro after ha kid key hk valid
      cases ha
      exact current d hd kid key hk valid
    · simpa only [ConfiguredIdentity.view,hd,Option.map_some,ConfiguredIdentity.state] using saved
  have finish : Hoare (do
      setRxSkb id fun q => {q with state}
      setPeer pid {p with napiScheduled := true}
      pure pid) Q (fun _ => Inv history) := by
    apply hoare_bind _ _ write
    intro _
    apply hoare_bind _ _ (CurrentTraffic.writePeer_spec history pid {p with napiScheduled := true})
    intro _
    exact preserves_pure _
  split
  · apply hoare_bind _ _ (hoare_liftAmbient
      (AmbientM.invariant "a decrypted packet that is not on its peer's rx_queue") Q)
    intro _
    exact finish
  · exact finish

private theorem congr (hg : CurrentChecks.Preserves g)
    (eq : ∀ w h, runPrefix g w h = runPrefix f w h) : CurrentChecks.Preserves f := by
  intro w h hi
  simpa only [← eq w h] using hg w h hi

private theorem mixed (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (he : ErasesPrefix g a) (hm : Retaining.ProductRetainsCall a)
    (hc : ∀ history, Preserves (fun w : World => Inv history w.wg) a) :
    CurrentChecks.Preserves (RxHistory.mixed g) := by
  apply CurrentChecks.quiet _ (Appends.focus _ _ _) _
    (HistorySupport.mixed g a he hm) (CurrentHistory.mixed g a he hc)
  intro w h
  unfold auditFocus
  rw [HistorySupport.focus_compose]
  exact focusPrefix_other _ _ sensitive (fun _ => rfl) g w h

private theorem native_mixed (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (he : ErasesStatePrefix g a) (hm : Retaining.RetainsCall a)
    (hc : ∀ history, Preserves (Inv history) a) :
    CurrentChecks.Preserves (RxHistory.mixed (liftWGObserver g)) :=
  mixed _ _ (liftWGObserver_erases he) hm.product (CurrentHistory.native_product a hc)

private def Focused (enc : E → RxHistory.Event) (dec : RxHistory.Event → Option E)
    (g : PrefixM E α) : Prop := Appends g ∧ CurrentChecks.Preserves (focusPrefix enc dec g)

private theorem focused_bind (enc : E → RxHistory.Event) (dec : RxHistory.Event → Option E)
    (inverse : ∀ e, dec (enc e) = some e) (g : PrefixM E α) (f : α → PrefixM E β)
    (hg : Focused enc dec g) (hf : ∀ x, Focused enc dec (f x)) :
    Focused enc dec (g >>= f) :=
  ⟨hg.1.bind (fun x => (hf x).1),
    congr (hg.2.bind (fun x => (hf x).2))
      (focusPrefix_bind_appends enc dec inverse hg.1 (fun x => (hf x).1))⟩

private theorem focused_pure (enc : E → RxHistory.Event) (dec : RxHistory.Event → Option E) (x : α) :
    Focused enc dec (pure x) := by
  refine ⟨Appends.pure x,?_⟩
  apply congr (PrefixPreserves.pure safe x)
  intro w h
  change (Except.ok (ε := Stop) (x,w),h) =
    (.ok (x,w),h ++ ((h.filterMap dec).drop (h.filterMap dec).length).map enc)
  simp

private theorem focused_lift (enc : E → RxHistory.Event) (dec : RxHistory.Event → Option E)
    (a : Leanux.M α) (hm : Retaining.ProductRetainsCall a)
    (hc : ∀ history, Preserves (fun w : World => Inv history w.wg) a) :
    Focused enc dec (liftPrefix a) := by
  refine ⟨Appends.lift a,?_⟩
  apply congr (CurrentChecks.quiet _ (Appends.lift a) (HistoryFrame.lift _ a)
    (HistorySupport.lift_retains a hm) (CurrentHistory.lift a hc))
  intro w h
  change (a.run w,h) =
    (a.run w,h ++ ((h.filterMap dec).drop (h.filterMap dec).length).map enc)
  simp

private theorem focused_ite (enc : E → RxHistory.Event) (dec : RxHistory.Event → Option E)
    (p : Prop) [Decidable p] (ha : p → Focused enc dec a) (hb : ¬p → Focused enc dec b) :
    Focused enc dec (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

private theorem rx_life (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (he : ErasesStatePrefix g a) (hm : Retaining.RetainsCall a)
    (hc : ∀ history, Preserves (Inv history) a) :
    Focused rxEncode rxDecode (liftWGObserver (focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? g)) := by
  refine ⟨(StateAppends.focus _ _ _).liftWGObserver,?_⟩
  change CurrentChecks.Preserves (focusPrefix rxEncode rxDecode (MaterialOrigin.access (liftWGObserver g)))
  apply CurrentChecks.quiet _ (Appends.focus _ _ _) _
    (HistorySupport.rx_life _ _ (liftWGObserver_erases he) hm.product)
    (CurrentHistory.rx_life _ _ (liftWGObserver_erases he) (CurrentHistory.native_product a hc))
  intro w h
  unfold MaterialOrigin.access
  rw [HistorySupport.focus_compose]
  exact focusPrefix_other _ _ sensitive (fun _ => rfl) _ w h

private theorem rx_decrypt (id : SkbId) :
    Focused rxEncode rxDecode (liftWGObserver (RxOrigin.decrypt id)) := by
  refine ⟨((StateAppends.focus _ _ _).receiptWGObserved _).liftWGObserver,?_⟩
  apply congr (CurrentChecks.decrypt id (CurrentRx.readDecrypt_preserves id))
  intro w h
  change runPrefix (focusPrefix HistoryAdapters.encode HistoryAdapters.decode
    (liftWGObserver (focusStatePrefix Origins.rxEncode Origins.rxDecode (RxOrigin.decrypt id)))) w h = _
  change runPrefix (focusPrefix HistoryAdapters.encode HistoryAdapters.decode
    (focusPrefix Origins.rxEncode Origins.rxDecode (liftWGObserver (RxOrigin.decrypt id)))) w h = _
  exact HistorySupport.focus_compose _ _ _ _ _ w h

open Lean Meta Elab Tactic in
elab "worker_focus_at " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Focused do throwError "not a focused worker contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing action"
  let mut action := args.back!.consumeMData
  if action.isAppOf ``liftWGObserver then
    let fields := action.getAppArgs
    unless fields.size > 0 do throwError "missing native action"
    action := fields.back!.consumeMData
  if (action.getAppFn.constName?.map Name.toString |>.getD "").endsWith ".accessState" then
    let fields := action.getAppArgs
    unless fields.size > 0 do throwError "missing focused action"
    action := fields.back!.consumeMData
  let expected ← realizeGlobalConstNoOverloadWithInfo wanted
  if expected != ``liftPrefix && action.isAppOf ``liftPrefix then
    let fields := action.getAppArgs
    unless fields.size > 0 do throwError "missing lifted action"
    action := fields.back!.consumeMData
    if action.isAppOf ``liftWG then
      let fields := action.getAppArgs
      unless fields.size > 0 do throwError "missing lifted native action"
      action := fields.back!.consumeMData
  unless action.getAppFn.constName? == some expected do throwError "different action"

theorem prepare : CurrentChecks.Preserves HistoryAdapters.prepare := by
  have get : Focused rxEncode rxDecode (liftPrefix (liftWG getDev)) :=
    focused_lift _ _ _
      (Retaining.RetainsCall.product (Retaining.of_view
        (Origins.sameView_of_sameWG (project := id) getDev_sameWGStore)))
      (CurrentHistory.native_product _ (native_store _ getDev_sameWGStore))
  have install (ring : PtrRing SkbId) : Focused rxEncode rxDecode
      (liftPrefix (liftWG (modifyDev fun d => {d with decryptQueue := ring}))) := by
    apply focused_lift
    · have material : Retaining.RetainsCall (modifyDev fun d => {d with decryptQueue := ring}) :=
        Retaining.of_view (Retaining.modifyDev_material _ (fun _ => rfl))
      exact material.product
    · apply CurrentHistory.native_product
      intro history
      current_lifecycle_step history
  have hp : Focused rxEncode rxDecode (liftWGObserver RxOrigin.prepare) := by
    unfold RxOrigin.prepare RxOrigin.prepareWith
    simp only [monadLift_self]
    repeat' first
      | (worker_focus_at getDev; exact get)
      | (worker_focus_at modifyDev; exact install _)
      | rw [liftWGObserver_lift]
      | rw [liftWGObserver_bind]
      | rw [liftWGObserver_pure]
      | (worker_focus_at RxOrigin.decrypt; exact rx_decrypt _)
      | (worker_focus_at setRxSkbPrefix
         apply rx_life _ _ (setRxSkbPrefix_erases _ _)
         · support_native_material
         · intro history; unfold setRxSkb; current_skb_step history)
      | (worker_focus_at RxWorkers.publishPrefix
         exact rx_life _ _ (RxWorkers.publish_erases _ _)
           (Retaining.of_view ((pinned_const _private.Leanux.Proofs.WG.Origins.SupportCallers.«0».Leanux.Proofs.WG.Origins.HistorySupport.publish_material) _ _))
           (publish_preserves _ _))
      | (worker_focus_at liftPrefix
         apply focused_lift
         · support_material
         · apply CurrentHistory.native_product
           intro history
           simp only [branch,invariant]
           first
           | exact native_store _ getDev_sameWGStore history
           | repeat' current_traffic_step history)
      | (worker_focus_at Pure.pure; exact focused_pure _ _ _)
      | (worker_focus_at Bind.bind; apply focused_bind _ _ rx_decode_encode)
      | (worker_focus_at ite; apply focused_ite)
      | support_intro
      | split
  apply congr hp.2
  intro w h
  exact (HistorySupport.focus_compose _ _ _ _ _ w h).symm

private theorem pending : CurrentChecks.Preserves (RxHistory.mixed (liftWGObserver RxNapi.pendingPrefix)) := by
  apply native_mixed _ _ RxNapi.pending_erases
  · apply Retaining.of_view
    intro initial
    unfold RxNapi.pendingSource
    repeat' material_basic (fun t => t = initial)
  · intro history
    unfold RxNapi.pendingSource
    repeat' current_lifecycle_step history

private theorem scheduled : CurrentChecks.Preserves (RxHistory.mixed (liftWGObserver RxNapi.scheduledPrefix)) := by
  apply native_mixed _ _ RxNapi.scheduled_erases
  · apply Retaining.of_view
    intro initial
    unfold RxNapi.scheduledSource
    repeat' material_basic (fun t => t = initial)
  · intro history
    unfold RxNapi.scheduledSource
    repeat' current_lifecycle_step history

theorem napiSoftirq : CurrentChecks.Preserves RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves safe store pending CurrentPoll.checked

theorem pollScheduledInline : CurrentChecks.Preserves RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves safe store pending CurrentPoll.checked

theorem napiIrqExit : CurrentChecks.Preserves RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves safe store scheduled napiSoftirq

private theorem pay (pid : PeerId) :
    CurrentChecks.Preserves (RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))) := by
  apply native_mixed _ _ (peerPutMixed_erases _)
    (Retaining.of_view (Retaining.peerPut_material _))
  intro history
  current_traffic_step history

theorem decryptStep : CurrentChecks.Preserves RxHistory.decryptStep := by
  unfold RxHistory.decryptStep RxWorkers.decryptWith
  apply PrefixPreserves.bind napiSoftirq
  intro _
  apply PrefixPreserves.bind prepare
  intro result
  cases result with
  | none => exact PrefixPreserves.pure safe false
  | some pid =>
    exact napiIrqExit.bind (fun _ => (pay pid).bind (fun _ =>
      napiSoftirq.bind (fun _ => PrefixPreserves.pure safe true)))

private theorem lift_store (a : Leanux.M α) (frame : SameProductStore a) :
    CurrentChecks.Preserves (liftPrefix a) := viewLiftPrefix_preserves productStoreView safe store frame

theorem decryptIteration : CurrentChecks.Preserves RxHistory.decryptIteration := by
  apply workerIterPrefix_preserves _ _ safe decryptStep
  apply PrefixPreserves.bind (lift_store _ (condResched_sameKernel _))
  intro b
  exact lift_store _ (by intro initial; exact productAmbient_spec (AmbientM.branch .decWorkerNeedResched b) _ (fun _ _ hi => hi))

private theorem product_store (a : Leanux.M α) (frame : SameProductStore a)
    (history : List SessionOrigin.Receipt) : Preserves (fun w : World => Inv history w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  have eq := (ProjectedAction.iff_run _ _ _).mp frame w x v hr
  have dev : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) eq
  refine ⟨?_,?_⟩
  · intro s hs
    exact hi.1 s (by simpa only [ConfiguredIdentity.view,dev] using hs)
  · intro d hd slot key hk valid
    exact hi.2 d (dev.symm.trans hd) slot key hk valid

private theorem encrypt_preserves (checksum : Packet → Leanux.M Packet)
    (hc : ∀ pkt history, Preserves (fun w : World => Inv history w.wg) (checksum pkt))
    (key : KeypairId) (pkt : DataPacket) (history : List SessionOrigin.Receipt) :
    Preserves (fun w : World => Inv history w.wg) (encryptPacket checksum key pkt) := by
  let P := fun w : World => Inv history w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    CurrentHistory.native_product _ (fun h => (calculateSkbPadding_sameWGWorld _ _).wp (Inv h)) history
  have checksumSpec (p : Packet) : Preserves P (checksum p) := hc p history
  have keySpec : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) := by
    apply CurrentHistory.native_product (getKeypair key)
    intro h
    current_traffic_step h
  routing_tx_source [encryptPacket] using [padding,checksumSpec,keySpec,ambient]

private theorem encryptTail_preserves (item : Option (List SkbId))
    (history : List SessionOrigin.Receipt) :
    Preserves (fun w : World => Inv history w.wg) (RxWorkers.encryptTailSource item) := by
  let P := fun w : World => Inv history w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have packet {α : Type} (a : SkbM α) : Preserves P (monadLift (liftSkb a) : Leanux.M α) := by
    apply CurrentHistory.native_product (liftSkb a)
    intro h
    current_skb_step h
  have encrypt (key : KeypairId) (pkt : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key pkt) :=
    encrypt_preserves _ (fun p h => (checksumHelp_sameWorld p).wp (fun w => Inv h w.wg)) key pkt history
  have enqueue (xs : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
    CurrentHistory.native_product _
      ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.enqueuePerPeerTx_preserves) xs state) history
  have stepSpec : Preserves P (RxWorkers.encryptStepTailSource item) := by
    routing_tx_source [RxWorkers.encryptStepTailSource,getTxSkb,setTxSkb] using [packet,encrypt,enqueue,ambient]
  have needSpec : Preserves P (Env.condResched .encryptWorker) :=
    product_store _ (condResched_sameKernel _) history
  routing_tx_source [RxWorkers.encryptTailSource,workerIter] using [stepSpec,needSpec,ambient]

theorem encryptIteration : CurrentChecks.Preserves RxHistory.encryptIteration := by
  unfold RxHistory.encryptIteration
  apply PrefixPreserves.bind
  · apply native_mixed _ _ (erasesStatePrefix_lift _)
    · apply Retaining.of_view
      intro initial
      unfold TxRing.pollSource
      repeat' material_basic (fun t => t = initial)
    · intro history
      unfold TxRing.pollSource
      repeat' current_lifecycle_step history
  · intro item
    apply PrefixPreserves.bind napiSoftirq
    intro _
    exact mixed _ _ (RxWorkers.encryptTail_erases item)
      ((pinned_const _private.Leanux.Proofs.WG.Origins.SupportCallers.«0».Leanux.Proofs.WG.Origins.HistorySupport.encryptTail_material) item)
      (encryptTail_preserves item)

end Leanux.Proofs.WG.CurrentWorkers
