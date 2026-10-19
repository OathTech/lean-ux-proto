import Leanux.Proofs.WG.AllowedIps.RoutingRxFrames
import Leanux.Proofs.Framing.WGReceiveHeaders

/-! Original receive admission is silent for routing, including normal error
cleanup. Resident peers may disappear; missing stores and record failures remain
original Stops. No packet/key/peer affiliation or initial residency is assumed. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.Queues Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem peerGetMaybeZero_routing (peer : Option PeerId) :
    SameView routingView (peerGetMaybeZero peer) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  have hb := ((hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.acquire_spec peer (wgStoreView w)) w ambient result v ambient' rfl hr).2
  cases result with
  | none =>
    change wgStoreView v = wgStoreView w at hb
    exact congrArg (fun store => store.dev.map routingState) hb
  | some pid =>
    obtain ⟨d, p, hd, hp, _, hk⟩ := hb
    have hs := routingState_insert_same d pid p {p with refcount := p.refcount + 1} hp rfl
    have hv := congrArg WGStoreView.dev hk
    change v.dev = some _ at hv
    change w.dev = some d at hd
    simp [routingView, hv, hd, hs]

theorem ownerSetWord_routing (owner : IndexOwner) (peer : Option PeerId) :
    SameView routingView (owner.setPeerWord peer) := by
  cases owner with
  | handshake pid =>
    exact modifyPeer_routing pid (fun p => {p with handshakeEntryPeer := peer}) (fun _ => rfl)
  | keypair kp =>
    exact (getKeypair_routing kp).bind fun k => setKeypair_routing kp {k with peer}

theorem indexLookup_routing (kinds : List IndexKind) (index : Nat) :
    SameView routingView (indexLookup kinds index) := by
  intro initial
  let P := fun w : WGWorld => routingView w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have table {α : Type} (a : IndexM α) : Preserves P (monadLift a : WG.M α) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    simpa only [P, routingView, hd, Option.map_some, routingState] using hi
  have peer := fun p => (peerGetMaybeZero_routing p).wp (fun view => view = initial)
  have word := fun o => (ownerWord_routing o).wp (fun view => view = initial)
  have write := fun o p => (ownerSetWord_routing o p).wp (fun view => view = initial)
  have loop {α β : Type} (xs : List α) (init : β)
      (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs init f) :=
    list_view_spec id P xs init f hf
  change Preserves P _
  unfold indexLookup
  simp only [branch, invariant]
  repeat' first
    | (allocation_release_lift_from IndexM; exact table _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (rx_retention_head peerGetMaybeZero; exact peer _)
    | (rx_retention_head IndexOwner.peerWord; exact word _)
    | (rx_retention_head IndexOwner.setPeerWord; exact write _ _)
    | (rx_retention_head ForIn.forIn; apply loop)
    | routing_tx_step

theorem enqueuePerDeviceAndPeerRx_routing (id : SkbId) :
    SameView routingView (enqueuePerDeviceAndPeerRx id) := by
  have packets {α : Type} (a : SkbM α) : SameView routingView (liftSkb a) := by
    intro initial
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa only [routingView, hd, Option.map_some, routingState] using hi
  have cpu := fun last => show SameView routingView _ from
    routing_kernel _ (cpumaskNextOnlineFrom_sameStore last)
  routing_handshake_source [enqueuePerDeviceAndPeerRx, getRxSkb, setRxSkb,
    queueDeviceWork] using [packets, cpu, modifyDev_routing]
  all_goals rfl

theorem consumeData_routing (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    RetainsRoutingCall (consumeData msg src ds) := by
  have hq (id : SkbId) : RetainsRoutingCall (enqueuePerPeerRx (pure ()) id .dead : WG.M Unit) := by
    let before : WG.M PeerId := do
      let pid ← IndexOwner.peerDeref (.keypair (← getRxSkb id).keypair)
      peerGet pid
      let p ← getPeer pid
      if !(p.rxQueue.all.contains id) then
        invariant "a decrypted packet that is not on its peer's rx_queue"
      setRxSkb id fun q => {q with state := .dead}
      setPeer pid {p with napiScheduled := true}
      pure pid
    have before_frame : SameView routingView before := by
      have packets {α : Type} (a : SkbM α) : SameView routingView (liftSkb a) := by
        intro initial
        apply hoare_liftSkb a
        intro w d store hi hd
        simpa only [routingView, hd, Option.map_some, routingState] using hi
      routing_handshake_source [before, getRxSkb, setRxSkb] using [packets, peerGet_routing]
    have factor : (enqueuePerPeerRx (pure ()) id .dead : WG.M Unit) =
        (do let pid ← before; peerPut (some pid)) := by
      have lift {α : Type} (a : WG.M α) : (liftM a : WG.M α) = a := rfl
      have bindIte {α β : Type} (c : Prop) [Decidable c]
          (a b : WG.M α) (f : α → WG.M β) :
          ((if c then a else b) >>= f) = (if c then a >>= f else b >>= f) := by
        split <;> rfl
      simp only [enqueuePerPeerRx, before, lift, bind_assoc, pure_bind, bindIte]
    rw [factor]
    intro initial
    apply hoare_consequence
      (hoare_bind before (fun pid => peerPut (some pid))
        (before_frame.wp (RetainsRouting initial))
        (fun pid => RetainsRoutingCall.wp (peerPut_retainsRouting (some pid)) initial))
    · intro w he
      change routingView w = initial at he
      rw [he]
      exact RetainsRouting.refl _
    · exact fun _ _ h => h
  intro initial
  let Q := RetainsRouting initial
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa only [P, routingView, hd, Option.map_some, routingState] using hi
  have lookup := (indexLookup_routing [.keypair] (u32le msg 4)).wp Q
  have key := fun kp => (keypairGet_routing kp).wp Q
  have peer := fun pid => (getPeer_routing pid).wp Q
  have enqueue := fun id => (enqueuePerDeviceAndPeerRx_routing id).wp Q
  have queue := fun id => RetainsRoutingCall.wp (hq id) initial
  have putKey := fun kp => (keypairPut_routing kp false).wp Q
  have putPeer := fun pid => RetainsRoutingCall.wp (peerPut_retainsRouting pid) initial
  have main : Preserves P (consumeData msg src ds) := by
    unfold consumeData newRxSkb freeRxSkb keypairGetNull
    simp only [branch, WG.orM, invariant]
    repeat' first
      | (allocation_release_lift_from AmbientM; exact ambient _)
      | (rx_retention_head liftSkb; exact skb _)
      | (rx_retention_head indexLookup; exact lookup)
      | (rx_retention_head keypairGet; exact key _)
      | (rx_retention_head getPeer; exact peer _)
      | (rx_retention_head enqueuePerDeviceAndPeerRx; exact enqueue _)
      | (rx_retention_head enqueuePerPeerRx; exact queue _)
      | (rx_retention_head keypairPut; exact putKey _)
      | (rx_retention_head peerPut; exact putPeer _)
      | routing_tx_step
  apply hoare_consequence main
  · intro w h
    change routingView w = initial at h
    change RetainsRouting initial (routingView w)
    rw [h]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem cpumaskNextOnline_routing : SameView routingView cpumaskNextOnline := by
  routing_handshake_source [cpumaskNextOnline] using [modifyDev_routing]
  all_goals rfl

theorem packetReceive_routing (msg : List UInt8) (src : SkbSource) :
    RetainsRoutingCall (packetReceive msg src) := by
  intro initial
  let Q := RetainsRouting initial
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have header := (prepareSkbHeader_sameWGWorld msg).wp P
  have dsfield := fun protocol bytes => (ipTunnelGetDsfield_sameWGWorld protocol bytes).wp P
  have consume := fun ds => RetainsRoutingCall.wp (consumeData_routing msg src ds) initial
  have cpu := cpumaskNextOnline_routing.wp Q
  have device := (routing_kernel _ getDev_sameWGStore).wp Q
  have write := (modifyDev_routing (fun d => {d with
    handshakeQueue := d.handshakeQueue.produce (msg, src),
    handshakeQueueLen := d.handshakeQueueLen + 1}) (fun _ => rfl)).wp Q
  have main : Preserves P (packetReceive msg src) := by
    unfold packetReceive
    simp only [branch, invariant, unsupported, queueDeviceWork]
    repeat' first
      | (allocation_release_lift_from AmbientM; exact ambient _)
      | (rx_retention_head prepareSkbHeader; exact header)
      | (rx_retention_head ipTunnelGetDsfield; exact dsfield _ _)
      | (rx_retention_head consumeData; exact consume _)
      | (rx_retention_head cpumaskNextOnline; exact cpu)
      | (rx_retention_head getDev; exact device)
      | (rx_retention_head modifyDev; exact write)
      | routing_tx_step
  apply hoare_consequence main
  · intro w h
    change routingView w = initial at h
    change RetainsRouting initial (routingView w)
    rw [h]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem wgReceive_routing (msg : List UInt8) (src : SkbSource) :
    RetainsRoutingCall (wgReceive msg src) := by
  intro initial
  let P := fun w : WGWorld => RetainsRouting initial (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have packet := RetainsRoutingCall.wp (packetReceive_routing msg src) initial
  have main : Preserves P (wgReceive msg src) := by
    unfold wgReceive
    simp only [branch, unsupported]
    repeat' first
      | (allocation_release_lift_from AmbientM; exact ambient _)
      | (rx_retention_head packetReceive; exact packet)
      | routing_tx_step
  apply hoare_consequence main
  · intro w h
    change routingView w = initial at h
    change RetainsRouting initial (routingView w)
    rw [h]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

end Leanux.Proofs.WG.AllowedIps
