import Leanux.Proofs.WG.AuthenticatedEffects.TransportJournalOrder

/-! Initialized replay authentication and immediate confirmation attribution
are proved over one full shared journal, including every retained Stop prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportJournal
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues TransmitSecurity TransportCarrier Journal HandshakeSecurity

private theorem state_join {g : WGPrefix Event α} (carrier : StateSafe g)
    (order : Driver.StateHistorySafe Order.Good g) :
    TransportCarrier.StateSafe Order.Good origin? replay? g := by
  intro w a h hi
  obtain ⟨suffix,appended,safe,normal⟩ := carrier w a h ⟨hi.1,hi.2.1,True.intro⟩
  obtain ⟨_,_,ordered,after⟩ := order w a h hi.2.2
  refine ⟨suffix,appended,⟨safe.1,ordered⟩,?_⟩
  cases run : (runPrefix (g.run w) a h).1 with
  | error err => trivial
  | ok out =>
    simp only [run] at normal after ⊢
    exact ⟨normal.1,normal.2.1,after⟩

private theorem product_join {g : PrefixM Event α} (carrier : ProductSafe g)
    (order : Driver.ProductHistorySafe Order.Good g) :
    TransportCarrier.ProductSafe Order.Good origin? replay? g :=
  product_combine g (base carrier) order

private theorem keepalive_order (pid : PeerId) :
    Driver.StateHistorySafe Order.Good (Driver.keepaliveObserved Journal.hooks pid) := by
  unfold Driver.keepaliveObserved
  repeat' first
    | (driver_history_head Driver.stagingObserved; exact ConfirmationTransportOrder.quiet_staging Order.quiet _)
    | driver_state_history_step

theorem ordered_callbacks : DeferredSafe Order.Good origin? replay? Journal.hooks where
  armTimer := fun pid timer delay caller => state_join (armTimer pid timer delay caller) (Order.quiet.armTimer pid timer delay caller)
  queueSend := fun pid => state_join (queueSend pid) (Order.quiet.queueSend pid)
  selection := fun pid => state_join (selection pid) (Order.quiet.selection pid)
  reserve := fun kid => state_join (reserve kid) (Order.quiet.reserve kid)
  allocate := fun packets => state_join (allocate packets) (Order.quiet.allocate packets)
  create := fun pid item => state_join (create pid item) (Order.quiet.create pid item)
  prepare := product_join prepare Order.quiet.prepare
  poll := product_join poll Order.quiet.poll
  encrypt := fun item => product_join (encrypt item) (Order.quiet.encrypt item)
  transmit := fun pid => product_join (transmit pid) (Order.quiet.transmit pid)
  handshake := state_join handshake
    (Order.quiet.handshake Journal.session (Driver.keepaliveObserved Journal.hooks)
      Order.quiet.session keepalive_order)
  napi := fun pid budget => product_join (nativePoll pid budget) (Order.nativePoll pid budget)
  sendWorker := product_join sendWorker Order.quiet.sendWorker
  flushedSend := fun pid => state_join (flushedSend pid) (Order.quiet.flushedSend pid)
  selected := fun d j pid t entry => product_join (timer d j pid t entry) (Order.quiet.timerSelected d j pid t entry)

/-- Both independent positional claims hold on the actual initialized full
journal. No assumed native packet, callback authorization or receipt order
remains in the theorem's inputs. -/
theorem initialized_ordered (trace : Runner.Trace) (placeholders : Bool) :
    TransportReplay.Safe origin? replay? (runPrefixOuter (Journal.execute trace placeholders) []).2 ∧
    Order.Good (runPrefixOuter (Journal.execute trace placeholders) []).2 :=
  TransportCarrier.initialized ordered_callbacks
    (fun family addr packets mtu => state_join (front family addr packets mtu)
      (Order.quiet.front family addr packets mtu))
    (by intro pre event post position; cases pre <;> cases position) trace placeholders

/-- Every observed native confirmation follows the actual successful replay
check for that peer and key, whose selected packet has a strictly earlier native
AEAD publication. The certificate survives a later stopped consumer. -/
theorem confirmation_authenticated (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (event : Event) (pid : PeerId) (kid : KeypairId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (Journal.execute trace placeholders) []).2 = pre ++ event :: post)
    (recorded : responder? event = some (.confirmed pid kid r)) :
    r.Valid (receivedWithKeypair pid kid) ∧
    ∃ earlier counter, pre = earlier ++ [Event.replay counter] ∧
      counter.packet.peer = pid ∧ counter.packet.keypair = kid ∧ counter.run.value = true ∧
      TransportReplay.Certified (earlier.filterMap origin?) counter := by
  have safe := initialized_ordered trace placeholders
  exact ConfirmationTransportOrder.authenticated origin? replay? Event.replay responder? (fun _ => rfl)
    _ pre post event pid kid r safe.2 safe.1 position recorded

end Leanux.Proofs.WG.AuthenticatedEffects.TransportJournal
