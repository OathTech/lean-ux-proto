import Leanux.Proofs.WG.TransmitSecurity.DriverGroNeutral
import Leanux.Proofs.WG.AuthenticatedEffects.TransportJournalStaging
import Leanux.Proofs.WG.AuthenticatedEffects.TransportWorkerFrames
import Leanux.Proofs.WG.TransmitSecurity.DriverNeutralCalls

/-! Concrete ring, encryption, completion and timer selection hooks retain
RX authentication certificates and cannot invent a replay receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity TransportCarrier Journal

theorem poll : ProductSafe Journal.poll :=
  product_quiet (Appends.focus _ _ _).receiptObserved
    (HistoryFrame.receiptObserved (focusPrefix_other _ _ replay? (fun _ => rfl) _) (fun _ => rfl))
    (product_erases handshake? Journal.HandshakeProjection.poll)
    (TransportHookFrames.wg _ TransportHookFrames.poll)

theorem encrypt (item : Option (List SkbId)) : ProductSafe (Journal.encrypt item) :=
  product_quiet (Appends.focus _ _ _).receiptObserved
    (HistoryFrame.receiptObserved (focusPrefix_other _ _ replay? (fun _ => rfl) _) (fun _ => rfl))
    (product_erases handshake? (Journal.HandshakeProjection.encrypt item))
    (TransportHookFrames.encrypt item)

theorem transmit (pid : PeerId) : ProductSafe (Journal.transmit pid) :=
  product_quiet (Appends.focus _ _ _)
    (focusPrefix_other completionEvent completion? replay? (fun e => by cases e <;> rfl) _)
    (product_erases handshake? (Journal.HandshakeProjection.transmit pid))
    (TransportHookFrames.wg _ (TransportHookFrames.transmit pid))

theorem prepare : ProductSafe Journal.hooks.prepare := by
  apply product_combine _ (TransportReplay.prepare_checked Event.rxOrigin origin? replay? (fun _ => rfl) (fun _ => rfl))
  intro w h _
  obtain ⟨suffix,eq⟩ := Appends.focus Event.rxOrigin origin? (liftWGObserver RxOrigin.prepare) w h
  exact ⟨suffix,eq,True.intro,by split <;> trivial⟩

theorem sendWorker : ProductSafe (Driver.sendWorkerObserved Journal.hooks) := by
  rw [Driver.sendWorker_lift Journal.hooks rfl]
  exact product_rx _ TransportHookFrames.sendWorker

theorem flushedSend (pid : PeerId) : StateSafe (Journal.hooks.flushedSend pid) :=
  state_rx _ ((TransportRemoval.flushedSend_geometry pid).factor Prod.snd)

theorem timer (d : Device) (j : UInt64) (pid : PeerId) (t : PeerTimer) (entry : WheelEntry) :
    ProductSafe (Journal.hooks.timerSelected d j pid t entry) := by
  apply product_quiet (TimerDispatch.scope_appends _ _ _ _ _ _ (Appends.pure _))
  · intro w h
    rw [TimerDispatch.scope_run,runPrefix_pure]
    simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,replay?,List.append_nil]
  · exact TimerDispatch.scope_erases _ _ _ _ _ _ (erasesPrefix_pure 0)
  · exact SameView.pure _ _

theorem timerFinished (token : Nat) : ProductSafe (Journal.hooks.timerFinished token) :=
  product_pure ()

theorem base {g : PrefixM Journal.Event α} (safe : ProductSafe g) :
    TransportReplay.Preserves (origin := origin?) (replay := replay?) g := by
  unfold TransportReplay.Preserves TransportReplay.Inv
  simpa only [ProductSafe,TransportCarrier.ProductSafe,and_true] using safe

theorem nativePoll (pid : PeerId) (budget : Nat) :
    ProductSafe (Driver.nativePollObserved Journal.hooks pid budget) := by
  rw [Driver.nativePoll_neutral _ rfl rfl]
  have carrier := TransportReplay.poll_checked origin? replay? Event.replay (fun _ => rfl) (fun _ => rfl)
    (fun pid pkt ep => liftWGObserver (Driver.consumeObserved Journal.hooks pid pkt ep))
    (napiGroReceivePrefix (Driver.stackFlushObserved Journal.hooks))
    (napiGroFlushAllPrefix (Driver.stackFlushObserved Journal.hooks))
    (fun pid pkt ep => base (product_state (TransportCarrier.consume staging confirmation pid pkt ep)))
    (fun gro bytes => base (gro_receive _ (TransportCarrier.flush staging front) gro bytes))
    (fun gro => base (gro_flush _ (TransportCarrier.flush staging front) gro)) pid budget
  unfold TransportReplay.Preserves TransportReplay.Inv at carrier
  simpa only [ProductSafe,TransportCarrier.ProductSafe,and_true,liftWGObserver_lift,
    Driver.pollObserved,Journal.hooks,CandidatePoll.neutral] using carrier

end Leanux.Proofs.WG.AuthenticatedEffects.TransportJournal
