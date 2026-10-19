import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionStaging
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionRoutingFrames

/-! Actual routing handoff, authenticated receive completion and decrypt
publication retain ordered socket accounting. Packet authentication and
causal authorization are supplied by their existing independent predicates. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing TransmitSecurity Lifetimes
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private theorem native_appends (action : WG.M α) : StateAppends (liftWGPrefix action : WGPrefix Journal.Event α) :=
  fun _ _ _ => ⟨[],by simp only [List.append_nil]; rfl⟩

theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (hooks.front family addr packets mtu) :=
  old_state _ _ (receiptWGObserved_erases (erasesStatePrefix_lift _) _)
    ((native_appends _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun _ _ _ => rfl) _ (fun _ => rfl))
    (EmissionFrames.front family addr packets mtu)

theorem device_transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (Driver.transmitObserved hooks family addr packets mtu) := by
  unfold Driver.transmitObserved
  apply state_bind (front family addr packets mtu)
  intro result
  cases result with
  | error err => exact state_pure err
  | ok pid => exact state_bind (staging pid) (fun _ => state_bind
      (state_native _ (peerPut_sent (some pid))) (fun _ => state_pure _))

theorem fresh_receive (pid : PeerId) : StateSafe (PacketEffects.freshReceiveWith effects pid) := by
  unfold PacketEffects.freshReceiveWith
  repeat' first
    | (emission_head TimerEffects.Ops.step; change StateSafe (liftWGPrefix _))
    | (emission_head TimerEffects.queuedWith; exact queued _ _)
    | (emission_native_head WG.andM; apply state_native
       sent_frame [] using [getKeypair_sent_spec,expired_sent_spec])
    | emission_effect_step

private theorem stats (pid : PeerId) (len : Nat) : StateSafe (effects.step (updateRxStats pid len)) := by
  apply state_native
  sent_frame [updateRxStats] using [getPeer_sent_spec,setPeer_sent_spec]

private theorem dishonest_frame (why : Dishonest) : StateSafe (effects.step (dishonest why)) := by
  apply state_native
  cases why <;> sent_frame [dishonest] using []

private theorem ecn (protocol outer : Nat) (bytes : List UInt8) :
    StateSafe (effects.step (inetEcnDecapsulate protocol outer bytes)) := by
  apply state_native
  sent_frame [inetEcnDecapsulate,inetEcnSet,ipEcnSetCe,ip6EcnSetCe,ipEcnSetEct1,ip6EcnSetEct1] using []

theorem prepare (pid : PeerId) (packet : RxPacket) : StateSafe (PacketEffects.prepareWith effects pid packet) := by
  unfold PacketEffects.prepareWith
  repeat' first
    | (emission_head TimerEffects.Ops.step; change StateSafe (liftWGPrefix _))
    | (emission_head PacketEffects.freshReceiveWith; exact fresh_receive _)
    | (emission_native_head timersAnyAuthenticatedPacketReceived; exact state_native _ (EmissionFrames.delete _ _))
    | (emission_head TimerEffects.traversalWith; exact traversal _)
    | (emission_head TimerEffects.dataReceivedWith; exact data_received _)
    | (emission_native_head updateRxStats; exact stats _ _)
    | (emission_native_head dishonest; exact dishonest_frame _)
    | (emission_native_head inetEcnDecapsulate; exact ecn _ _ _)
    | emission_effect_step

theorem receive_tail (pid : PeerId) (packet : RxPacket) (confirmed : Bool) :
    StateSafe (Driver.receiveTailObserved hooks pid packet confirmed) := by
  unfold Driver.receiveTailObserved
  repeat' first
    | (emission_head Driver.stagingObserved; exact staging _)
    | (emission_head PacketEffects.prepareWith; exact prepare _ _)
    | (emission_native_head timersHandshakeComplete; exact state_native _ (EmissionFrames.completed _ _))
    | (emission_native_head Packets.rxFinish; exact state_native _ (EmissionFrames.receive_finish _ _))
    | emission_effect_native
    | emission_step

theorem consume (pid : PeerId) (packet : RxPacket) (ep : Endpoint) :
    StateSafe (Driver.consumeObserved hooks pid packet ep) := by
  unfold Driver.consumeObserved
  exact state_bind (state_native _ (EmissionFrames.endpoint_value pid ep)) (fun _ =>
    state_bind (confirmation pid packet.keypair) (receive_tail pid packet))

theorem decrypt_prepare : ProductSafe hooks.prepare :=
  old_product _ _ (TransportDriver.prepare_erases _ _) (Appends.focus _ _ _)
    (fun w h => focusPrefix_other _ _ oldSocket? (fun _ => rfl) _ w h) decryptPrepare_sent

private theorem counter_native (key : KeypairId) (nonce : Nat) : SameView WGWorld.sent (counterValidate key nonce) := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  have loop {α β : Type} (xs : List α) (init : β) (body : α → β → WG.M (ForInStep β))
      (safe : ∀ value state, Preserves (fun w : WGWorld => w.sent = initial) (body value state)) :
      Preserves (fun w : WGWorld => w.sent = initial) (forIn xs init body) :=
    list_view_spec id (fun w : WGWorld => w.sent = initial) xs init body safe
  unfold counterValidate
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',WG.orM,branch,branchCmp]
  repeat' first
    | (cookie_source_head ForIn.forIn; apply loop; intro value state)
    | consumer_sent_step initial

theorem counter (skb : SkbId) (packet : RxPacket) : ProductSafe (hooks.counterCheck skb packet) := by
  apply old_product _ _ (TransportDriver.counter_erases _ _ _) ((Appends.lift _).receiptObserved)
    (HistoryFrame.receiptObserved (HistoryFrame.lift oldSocket? _) (fun _ => rfl))
  exact counter_native _ _

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
