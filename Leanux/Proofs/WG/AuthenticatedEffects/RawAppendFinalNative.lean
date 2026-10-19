import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendFinalSource
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalCallbackProjection

/-! Non-sending final callbacks retain their native effects and produce no raw
socket append. These are exact callback projections, including stopped runs,
not a conclusion drawn from equality of final socket buffers. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend.Final
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

theorem state_native (body : WGPrefix Journal.Event α) (native : WG.M α)
    (appends : StateAppends body)
    (project : StateProjectsPrefix journal? id body (liftWGPrefix native)) :
    StateProjectsPrefix raw? id (CausalJournal.state body) (liftWGPrefix native) :=
  fun w => focused_projects CausalJournal.Event.old CausalJournal.old? journal? raw?
    (fun _ => rfl) (body.run w) ((liftWGPrefix native).run w) (appends w)
    (Independent.lift _) (project w)

theorem product_native (body : PrefixM Journal.Event α) (native : Leanux.M α)
    (appends : Appends body) (project : ProjectsPrefix journal? id body (liftPrefix native)) :
    ProjectsPrefix raw? id (CausalJournal.product body) (liftPrefix native) :=
  focused_projects CausalJournal.Event.old CausalJournal.old? journal? raw?
    (fun _ => rfl) body (liftPrefix native) appends (Independent.lift _) project

theorem selection (pid : PeerId) :
    StateProjectsPrefix raw? id (CausalJournal.hooks.selection pid) (RawAppend.hooks.selection pid) :=
  HandshakeSecurity.ExchangeCausal.Callbacks.selection raw? (fun _ => rfl) (fun _ _ => rfl) pid

theorem confirmation (pid : PeerId) (kid : KeypairId) :
    StateProjectsPrefix raw? id (CausalJournal.hooks.confirmation pid kid) (RawAppend.hooks.confirmation pid kid) :=
  state_native _ _ (StateAppends.focus _ _ _)
    (fun w => projectsPrefix_focus_other Journal.Event.responder Journal.responder? journal? (fun _ => rfl)
      (HandshakeSecurity.Responder.DriverCuts.confirmation_erases pid kid w))

theorem session (pid : PeerId) :
    StateProjectsPrefix raw? id (CausalJournal.hooks.session pid) (RawAppend.hooks.session pid) :=
  HandshakeSecurity.ExchangeJoint.session_ignored raw? CausalJournal.Event.exchange (fun _ => rfl) pid _ _
    (state_native _ _ (StateAppends.focus _ _ _)
      (fun w => projectsPrefix_focus_other Journal.Event.responder Journal.responder? journal? (fun _ => rfl)
        (HandshakeSecurity.Responder.DriverCuts.session_erases pid w)))

theorem reserve (slot : KeypairId) :
    StateProjectsPrefix raw? id (CausalJournal.hooks.reserve slot) (RawAppend.hooks.reserve slot) :=
  state_native _ _ ((StateAppends.focus _ _ _).receiptWGObserved _)
    (Journal.state_receipt_projects journal? _ _ _ (fun _ => rfl)
      (fun w => projectsPrefix_focus_other Journal.Event.nonce Journal.nonce? journal? (fun _ => rfl)
        (Nonce.reserveObserved_erases slot w)))

theorem allocate (packets : List DataPacket) :
    StateProjectsPrefix raw? id (CausalJournal.hooks.allocate packets) (RawAppend.hooks.allocate packets) :=
  state_native _ _ ((StateAppends.lift _).receiptWGObserved _)
    (Journal.state_receipt_projects journal? _ _ _ (fun _ => rfl) (Driver.Projection.state_lift journal? _))

theorem create (pid : PeerId) (item : List SkbId) :
    StateProjectsPrefix raw? id (CausalJournal.hooks.create pid item) (RawAppend.hooks.create pid item) :=
  HandshakeSecurity.ExchangeCausal.Callbacks.create raw? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid item

theorem prepare : ProjectsPrefix raw? id CausalJournal.hooks.prepare RawAppend.hooks.prepare :=
  product_native _ _ (Appends.focus _ _ _)
    (TransportDriver.prepare_projects_other Journal.Event.rxOrigin Journal.origin? journal? (fun _ => rfl))

theorem counter (skb : SkbId) (packet : RxPacket) :
    ProjectsPrefix raw? id (CausalJournal.hooks.counterCheck skb packet) (RawAppend.hooks.counterCheck skb packet) :=
  product_native _ _ ((Appends.lift _).receiptObserved)
    (TransportDriver.counter_projects_other Journal.Event.replay journal? (fun _ => rfl) skb packet)

theorem poll : ProjectsPrefix raw? id CausalJournal.hooks.poll RawAppend.hooks.poll :=
  product_native _ _ ((Appends.focus _ _ _).receiptObserved)
    (receiptObserved_projects (fun _ => rfl)
      (projectsPrefix_focus_other Journal.Event.ring Journal.ring? journal? (fun _ => rfl) TxRing.poll_erases))

theorem encrypt (item : Option (List SkbId)) :
    ProjectsPrefix raw? id (CausalJournal.hooks.encrypt item) (RawAppend.hooks.encrypt item) :=
  HandshakeSecurity.ExchangeCausal.Callbacks.encrypt raw? (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) item

theorem restore (pid : PeerId) (packets : List Packet) :
    StateProjectsPrefix raw? id (CausalJournal.hooks.stagedRestore pid packets) (RawAppend.hooks.stagedRestore pid packets) :=
  HandshakeSecurity.Exchange.quiet_native_projection raw? _ _
    (HandshakeSecurity.StagedConservation.Restore.observed_erases CausalJournal.Event.stagedRestored pid packets)
    (CausalJournal.CallbackQuiet.restore raw? (fun _ => rfl) pid packets).2

theorem front (family address : Nat) (packets : List Packet) (mtu : Nat) :
    StateProjectsPrefix raw? id (CausalJournal.hooks.front family address packets mtu)
      (RawAppend.hooks.front family address packets mtu) := by
  change StateProjectsPrefix raw? id
    (do emitStatePrefix (CausalJournal.Event.transmitInput ⟨family,address,packets,mtu⟩)
        receiptWGObserved
          (HandshakeSecurity.StagedConservation.Front.frontWith
            (HandshakeSecurity.StagedConservation.Front.observedOps CausalJournal.Event.stagedDisposal CausalJournal.stagedDisposal?)
            family address packets mtu)
          (fun r => .old (.routed family address packets mtu r))) _
  have entry : StateProjectsPrefix raw? id
      (emitStatePrefix (CausalJournal.Event.transmitInput ⟨family,address,packets,mtu⟩))
      (pure () : WGPrefix RawAppend.Event Unit) := by
    intro w a h
    change (Except.ok (((),w),a),h.filterMap raw?) =
      (Except.ok (((),w),a),(h ++ [CausalJournal.Event.transmitInput ⟨family,address,packets,mtu⟩]).filterMap raw?)
    simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,raw?,List.append_nil]
  have body := Journal.state_receipt_projects raw? _ _
    (fun r => CausalJournal.Event.old (.routed family address packets mtu r)) (fun _ => rfl)
    (HandshakeSecurity.StagedConservation.Front.observed_front_projects CausalJournal.Event.stagedDisposal
      CausalJournal.stagedDisposal? raw? (fun _ => rfl) ⟨family,address,packets,mtu⟩)
  simpa only [pure_bind,RawAppend.hooks] using StateProjectsPrefix.bind
    (f := fun (_ : Unit) => receiptWGObserved
      (HandshakeSecurity.StagedConservation.Front.frontWith
        (HandshakeSecurity.StagedConservation.Front.observedOps CausalJournal.Event.stagedDisposal CausalJournal.stagedDisposal?)
        family address packets mtu)
      (fun r => CausalJournal.Event.old (.routed family address packets mtu r)))
    (b := fun (_ : Unit) => liftWGPrefix (Packets.txFront family address packets mtu))
    raw? id id entry (fun _ => body)

theorem purge (pid : PeerId) :
    StateProjectsPrefix raw? id (CausalJournal.hooks.stagedPurge pid) (RawAppend.hooks.stagedPurge pid) :=
  HandshakeSecurity.Exchange.quiet_native_projection raw? _ _
    (focusStatePrefix_erases _ _ (HandshakeSecurity.StagedDisposal.purge_erases pid))
    (fun w => focusPrefix_other CausalJournal.Event.stagedDisposal CausalJournal.stagedDisposal? raw? (fun _ => rfl)
      ((HandshakeSecurity.StagedDisposal.purgeObserved pid).run w))

theorem release (peer : Option PeerId) :
    StateProjectsPrefix raw? id (CausalJournal.hooks.peerRelease peer) (RawAppend.hooks.peerRelease peer) :=
  HandshakeSecurity.StagedDisposal.Decoration.release_projects CausalJournal.Event.stagedDisposal
    CausalJournal.stagedDisposal? raw? (fun _ => rfl) peer

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend.Final
