import Leanux.Proofs.WG.Packets.PublicationPrepare
import Leanux.Proofs.WG.Origins.CurrentIndex
import Leanux.Proofs.WG.Origins.ConfiguredHandshake
import Leanux.Proofs.WG.Queues.RxPollReceiptLink

/-! Publication-to-consume identity on the existing selected-packet observer.
The original publication and its session witness stay fixed. Only the live
packet and current peer identity are transported; key validity need not persist.
Interleavings before capture must establish this live relation separately.
No initialized history or complete poll transport is asserted here. -/
namespace Leanux.Proofs.WG.PublicationIdentity
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues

/-- The exact published crypted packet is still selected at this allocation,
and its current peer has the published allocation stamp and static key. Other
packet cells, peer counters, timers, keys and queues are not constrained. -/
def Live (history : List SessionOrigin.Receipt) (id : SkbId)
    (r : WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket) (pid : PeerId)
    (published current : WGWorld) : Prop :=
  CurrentCertificate history id r out pid published ∧
  packetStamp current id = packetStamp published id ∧
  (RxDisposition.nativeRxStore current).2 id = some {out with state := .crypted} ∧
  (CurrentIdentity.peerView current).bind (fun peers => peers pid) =
    (CurrentIdentity.peerView published).bind (fun peers => peers pid)

variable {id : SkbId}

theorem CurrentCertificate.live (h : CurrentCertificate history id r out pid published) :
    Live history id r out pid published published := by
  obtain ⟨d,k,p,after,hd,hp,hk,hv,owner,supported,shape,aead,stamp,peer,ha,epoch,packet,finalPeer⟩ := h
  refine ⟨⟨d,k,p,after,hd,hp,hk,hv,owner,supported,shape,aead,stamp,peer,ha,epoch,packet,finalPeer⟩,
    rfl,?_,rfl⟩
  simp only [RxDisposition.nativeRxStore,ha,Option.bind_some,packet]

/-- Only the selected packet and peer identity need agree. This pointwise
rule permits unrelated allocations, removals and field updates. -/
theorem Live.transport_pointwise (h : Live history id r out pid published w)
    (stamp : packetStamp v id = packetStamp w id)
    (packet : (RxDisposition.nativeRxStore v).2 id = (RxDisposition.nativeRxStore w).2 id)
    (peer : (CurrentIdentity.peerView v).bind (fun peers => peers pid) =
      (CurrentIdentity.peerView w).bind (fun peers => peers pid)) :
    Live history id r out pid published v :=
  ⟨h.1,stamp.trans h.2.1,packet.trans h.2.2.1,peer.trans h.2.2.2⟩

theorem Live.transport (h : Live history id r out pid published w)
    (packets : RxDisposition.nativeRxStore v = RxDisposition.nativeRxStore w)
    (peers : CurrentIdentity.peerView v = CurrentIdentity.peerView w) :
    Live history id r out pid published v := by
  refine ⟨h.1,?_,by simpa only [packets] using h.2.2.1,by simpa only [peers] using h.2.2.2⟩
  have epoch := congrArg Prod.fst packets
  have stamp : packetStamp v id = packetStamp w id := by
    simpa only [RxDisposition.nativeRxStore,packetStamp] using
      congrArg (fun o : Option Nat => (o.getD 0,id+1)) epoch
  exact stamp.trans h.2.1

/-- The Context below is extracted from this certificate's own ByPeer support.
It remains usable when later key invalidation makes CurrentIdentity.Inv vacuous. -/
theorem Live.owner_identity (h : Live history id r out pid published w) :
    ∃ (run : WGRunWitness (Option SessionOrigin.Context)) (ctx : SessionOrigin.Context)
      (after : Device) (peer : Peer),
      SessionOrigin.Receipt.material pid run ∈ history ∧ run.Valid (SessionOrigin.front pid) ∧
      run.value = some ctx ∧ ConfiguredSession.Configured pid run.before ctx ∧
      w.dev = some after ∧ after.peers[pid]? = some peer ∧
      CurrentIdentity.identity peer = CurrentIdentity.identity ctx.peer := by
  obtain ⟨run,ctx,d,p,hm,hv,hr,hc,hd,hp,identity⟩ := h.1.owner_identity
  have current : (CurrentIdentity.peerView w).bind (fun peers => peers pid) =
      some (CurrentIdentity.identity p) := by
    rw [h.2.2.2]
    simp only [CurrentIdentity.peerView,hd,Option.map_some,Option.bind_some,hp]
  cases hw : w.dev with
  | none => simp [CurrentIdentity.peerView,hw] at current
  | some after =>
    simp only [CurrentIdentity.peerView,hw,Option.map_some,Option.bind_some] at current
    obtain ⟨peer,resident,same⟩ := Option.map_eq_some_iff.mp current
    exact ⟨run,ctx,after,peer,hm,hv,hr,hc,rfl,resident,same.trans identity⟩

theorem Live.selected (h : Live history id r out pid published w.wg) :
    RxDisposition.SelectedAt id (packetStamp published id) {out with state := .crypted} w :=
  ⟨h.2.1,h.2.2.1⟩

theorem Live.packet_peer (h : Live history id r out pid published w) : out.peer = pid := by
  obtain ⟨d,k,p,after,hd,hp,hk,hv,owner,supported,shape,rest⟩ := h.1
  have same := congrArg RxPacket.peer shape
  exact same.trans owner.symm

/-- Capture is the original second getter. Its actual returned fields are
the anchored packet and stamp, and it leaves the whole product World intact. -/
theorem capture_current (history : List SessionOrigin.Receipt) (id : SkbId)
    (r : WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket) (pid : PeerId)
    (published : WGWorld) (w v : World) (h : List RxJoint.Event)
    (pkt : RxPacket) (stamp : PacketStamp)
    (live : Live history id r out pid published w.wg)
    (hr : (runPrefix (RxJoint.capture id) w h).1 = .ok ((pkt,stamp),v)) :
    v = w ∧ pkt = {out with state := .crypted} ∧ stamp = packetStamp published id ∧
    Live history id r out pid published v.wg := by
  obtain ⟨rfl,selected⟩ := RxDisposition.capture_selected id w v h pkt stamp hr
  exact ⟨rfl,Option.some.inj (selected.2.symm.trans live.2.2.1),
    selected.1.symm.trans live.2.1,live⟩

private theorem drop_peerView (pid : PeerId) :
    SameView CurrentIdentity.peerView
      (do setPeer pid {(← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.dropPeeked}) := by
  apply CurrentIdentity.peerView_of_configured
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  repeat' configured_step initial

private theorem counter_peerView (kp : KeypairId) (nonce : Nat) :
    SameView CurrentIdentity.peerView (counterValidate kp nonce) := by
  intro initial
  let P := fun w : WGWorld => CurrentIdentity.peerView w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have read : Preserves P (getKeypair kp) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient k v ambient' hi hr
    rw [(Keypairs.getKeypair_current kp w v ambient ambient' k hr).1]
    exact hi
  have write (k : Keypair) : Preserves P (setKeypair kp k) := by
    unfold setKeypair modifyDev
    apply hoare_modify
    intro w hi
    simpa only [P,CurrentIdentity.peerView,Option.map_map,Function.comp_def] using hi
  change Preserves P _
  routing_tx_source [counterValidate] using [read,write,ambient]

private theorem native_peer_product {α : Type} {a : WG.M α}
    (ha : SameView CurrentIdentity.peerView a) :
    SameView (fun w : World => CurrentIdentity.peerView w.wg) (liftWG a) :=
  sameView_liftWG _ _ _ ha (fun _ _ _ h => h)

/-- Any actual observer with these two semantic frames transports the anchored
certificate. Its arbitrary product action and history remain unrestricted. -/
theorem live_observer {E α : Type} (g : PrefixM E α) (a : Leanux.M α)
    (erases : ErasesPrefix g a) (appends : Appends g)
    (packets : SameView RxDisposition.rxStore a)
    (peers : SameView (fun w : World => CurrentIdentity.peerView w.wg) a) :
    PrefixPreserves (fun _ w => Live history id r out pid published w.wg) (fun _ => True) g := by
  intro w h hi
  obtain ⟨suffix,hs⟩ := appends w h
  refine ⟨suffix,hs,True.intro,?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok result =>
    have source := (erases w h).symm.trans hr
    exact hi.transport
      ((ProjectedAction.iff_run _ _ _).mp packets w result.1 result.2 source)
      ((ProjectedAction.iff_run _ _ _).mp peers w result.1 result.2 source)

theorem live_drop (q occurrence id : Nat) (stamp : PacketStamp) :
    PrefixPreserves (fun _ w => Live history id r out pid published w.wg) (fun _ => True)
      (RxJoint.drop q occurrence id stamp) := by
  have access := live_observer (history := history) (id := id) (r := r)
    (out := out) (pid := pid) (published := published) (RxJoint.access (liftWGObserver (rxDropPeekedPrefix q))) _
    (RxJoint.access_erases (liftWGObserver_erases (rxDropPeekedPrefix_erases q)))
    (RxJoint.access_appends _) (RxDisposition.drop_rxStore q)
    (native_peer_product (drop_peerView q))
  unfold RxJoint.drop
  apply PrefixPreserves.bind access
  intro _ w h hi
  exact ⟨[.removed occurrence id stamp],rfl,True.intro,hi⟩

theorem live_counter (kp : KeypairId) (nonce : Nat) :
    PrefixPreserves (fun _ w => Live history id r out pid published w.wg) (fun _ => True)
      (RxJoint.access (liftWGObserver (counterValidatePrefix kp nonce))) :=
  live_observer _ _ (RxJoint.access_erases (liftWGObserver_erases (counterValidatePrefix_erases kp nonce)))
    (RxJoint.access_appends _) (RxDisposition.counter_rxStore kp nonce)
    (native_peer_product (counter_peerView kp nonce))

theorem live_endpoint (source : SkbSource) :
    PrefixPreserves (fun _ w => Live history id r out pid published w.wg) (fun _ => True)
      (liftPrefix (liftWG (endpointFromSkb source)) : RxJoint.Obs (Option Endpoint)) := by
  apply live_observer _ _ (erasesPrefix_lift _) (Appends.lift _)
  · exact (liftWG_sameProductStore _ (endpointFromSkb_sameWGStore source)).of_factor
      (fun s : ProductStore43 => (s.2.2.2.dev.map (fun d => d.ifindex),
        fun id : SkbId => s.2.2.2.dev.bind (fun d => d.rxSkbs[id]?))) _ (fun _ => rfl)
  · apply native_peer_product
    exact CurrentIdentity.peerView_of_configured
      (ConfiguredIdentity.sameWG (project := fun w => w) (endpointFromSkb_sameWGStore source))

/-- A valid source-linked consume receipt retains the whole publication
certificate at its entry, even if its normal tail frees the packet or peer. -/
def ConsumeCertificate (history : List SessionOrigin.Receipt) (id : SkbId)
    (r : WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket) (pid : PeerId)
    (published : WGWorld) (stamp : PacketStamp) (receipt : RxDisposition.ConsumeReceipt) : Prop :=
  RxLink.Source id stamp receipt ∧ Live history id r out pid published receipt.run.before ∧
  receipt.packet = {out with state := .crypted} ∧ receipt.peer = pid

theorem live_receipt (live : Live history id r out pid published receipt.run.before)
    (source : RxLink.Source id stamp receipt) :
    ConsumeCertificate history id r out pid published stamp receipt := by
  have packet : receipt.packet = {out with state := .crypted} :=
    Option.some.inj (source.2.1.2.symm.trans live.2.2.1)
  refine ⟨source,live,packet,?_⟩
  have peer := source.2.2
  rw [packet] at peer
  exact peer.symm.trans live.packet_peer

/-- The actual consume caller is identified at its entry, independently of
what cleanup later removes. The history/context comes from the same publication. -/
theorem ConsumeCertificate.owner_identity
    (h : ConsumeCertificate history id r out pid published stamp receipt) :
    ∃ (run : WGRunWitness (Option SessionOrigin.Context)) (ctx : SessionOrigin.Context)
      (d : Device) (peer : Peer),
      SessionOrigin.Receipt.material receipt.peer run ∈ history ∧
      run.Valid (SessionOrigin.front receipt.peer) ∧ run.value = some ctx ∧
      ConfiguredSession.Configured receipt.peer run.before ctx ∧
      receipt.run.before.dev = some d ∧ d.peers[receipt.peer]? = some peer ∧
      CurrentIdentity.identity peer = CurrentIdentity.identity ctx.peer := by
  rw [h.2.2.2]
  exact h.2.1.owner_identity

/-- This is the existing once-only consume observer: its actual normal receipt
is emitted before optional buffering. Failed consume prefixes emit no receipt. -/
theorem consume_current (history : List SessionOrigin.Receipt) (id occurrence : Nat)
    (r : WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket) (pid : PeerId)
    (published : WGWorld) (ep : Endpoint) (w v : World) (h t : List RxJoint.Event)
    (value : Option RxJoint.Entry) (live : Live history id r out pid published w.wg)
    (hr : runPrefix (RxJoint.consume pid occurrence id (packetStamp published id)
      {out with state := .crypted} ep) w h = (.ok (value,v),t)) :
    ∃ receipt pre suffix,
      receipt.run.before = w.wg ∧ receipt.run.ambientBefore = w.ambient ∧
      receipt.run.after = v.wg ∧ receipt.run.ambientAfter = v.ambient ∧
      ConsumeCertificate history id r out pid published (packetStamp published id) receipt ∧
      t = h ++ pre ++ [.consumed occurrence id (packetStamp published id) receipt] ++ suffix ∧
      ∀ e, value = some e → e.origin = some receipt ∧ receipt.run.value = some e.tag.bytes := by
  have erases := RxJoint.access_erases
    (liftWGObserver_erases (consumeDataDonePrefix_erases pid {out with state := .crypted} ep)) w h
  obtain ⟨pre,hpre⟩ := RxJoint.access_appends
    (liftWGObserver (consumeDataDonePrefix pid {out with state := .crypted} ep)) w h
  rw [RxJoint.consume_run] at hr
  cases run : runPrefix (RxJoint.access
      (liftWGObserver (consumeDataDonePrefix pid {out with state := .crypted} ep))) w h with
  | mk result hist =>
    simp only [run] at hr erases hpre
    cases result with
    | error err => cases hr
    | ok result =>
      rcases result with ⟨returned,after⟩
      let receipt : RxDisposition.ConsumeReceipt :=
        ⟨pid,{out with state := .crypted},ep,⟨returned,w.wg,after.wg,w.ambient,after.ambient⟩⟩
      have valid : receipt.Valid := by
        change ((consumeDataDone pid {out with state := .crypted} ep).run w.wg).run w.ambient =
          .ok ((returned,after.wg),after.ambient)
        have equation := erases.symm
        rw [liftWG_run] at equation
        cases native : ((consumeDataDone pid {out with state := .crypted} ep).run w.wg).run w.ambient with
        | error stop => simp [native,Except.map] at equation
        | ok pair =>
          rcases pair with ⟨⟨x,g⟩,ambient⟩
          simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at equation
          obtain ⟨rfl,rfl⟩ := equation
          rfl
      have cert : ConsumeCertificate history id r out pid published (packetStamp published id) receipt :=
        live_receipt live ⟨valid,⟨live.2.1,live.2.2.1⟩,live.packet_peer⟩
      cases returned with
      | none =>
        cases hr
        refine ⟨receipt,pre,[],rfl,rfl,rfl,rfl,cert,?_,?_⟩
        · simp only [hpre,List.append_nil]
          rfl
        · intro e impossible
          cases impossible
      | some bytes =>
        cases hr
        refine ⟨receipt,pre,[.buffered ⟨⟨occurrence,id,bytes⟩,packetStamp published id,some receipt⟩],
          rfl,rfl,rfl,rfl,cert,?_,?_⟩
        · simp only [hpre]
          rfl
        · intro e eq
          cases eq
          exact ⟨rfl,rfl⟩

end Leanux.Proofs.WG.PublicationIdentity
