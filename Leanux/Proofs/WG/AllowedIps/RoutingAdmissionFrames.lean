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
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => routingView w = s)
        (fun _ w => routingView w = s) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    simpa only [routingView, hd, Option.map_some, routingState] using hi
  unfold Hoare at ambient table
  have hp := fun peer => (peerGetMaybeZero_routing peer).wp (fun t => t = s)
  have hw := fun owner => (ownerWord_routing owner).wp (fun t => t = s)
  have hs := fun owner peer => (ownerSetWord_routing owner peer).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec (m := AmbientM) routingView
    (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, -Std.Do.Spec.forIn_list,
    -Std.Do.Spec.forIn'_list, hl, ambient, table, indexLookup, hp, hw, hs,
    branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜routingView w = s⌝) :
    PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView]

theorem enqueuePerDeviceAndPeerRx_routing (id : SkbId) :
    SameView routingView (enqueuePerDeviceAndPeerRx id) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    hoare_liftAmbient a _
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => routingView w = s)
        (fun _ w => routingView w = s) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa only [routingView, hd, Option.map_some, routingState] using hi
  unfold Hoare at ambient skb
  have hp := fun pid => routing_getPeer (fun t => t = s) pid
  have hset := fun pid p => routing_setPeer (fun t => t = s) pid p
  have hc (last : Int) : Hoare (cpumaskNextOnlineFrom last)
      (fun w => routingView w = s) (fun _ w => routingView w = s) := by
    unfold Hoare
    mvcgen [cpumaskNextOnlineFrom, branch, AmbientM.branch]
  unfold Hoare at hc
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, skb,
    enqueuePerDeviceAndPeerRx, getRxSkb, setRxSkb, hp, hset, hc,
    getDev, modifyDev, queueDeviceWork, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals
    have lists (g : WGWorld) (pid : PeerId) :
        (g.dev.bind fun d => d.peers[pid]?.map (·.allowedipsList)) =
          (routingView g).bind (fun v => v.lists pid) := by
      simp [routingView, routingState, Option.bind_map, Function.comp_def]
    simp only [lists] at *
    rcases ‹routingView _ = s ∧ _› with ⟨he, hl⟩
    simp_all [routingView, routingState, Option.map_map, Function.comp_def]
  all_goals assumption

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
      apply SameView.of_wp
      intro initial
      have skb {α : Type} (a : SkbM α) :
          Hoare (liftSkb a) (fun w => routingView w = initial)
            (fun _ w => routingView w = initial) := by
        apply hoare_liftSkb a
        intro w d store hi hd
        simpa only [routingView, hd, Option.map_some, routingState] using hi
      unfold Hoare at skb
      have hg := fun pid => (peerGet_routing pid).wp (fun v => v = initial)
      have hp := routing_getPeer (fun v => v = initial)
      have hs := routing_setPeer (fun v => v = initial)
      have hw := fun o => (ownerDeref_routing o).wp (fun v => v = initial)
      mvcgen [before, getRxSkb, setRxSkb, skb, hg, hp, hs, hw,
        invariant, AmbientM.invariant]
      all_goals try dsimp +zetaDelta only at *
      all_goals try simp_all
      all_goals
        have lists (g : WGWorld) (pid : PeerId) :
            (g.dev.bind fun d => d.peers[pid]?.map (·.allowedipsList)) =
              (routingView g).bind (fun v => v.lists pid) := by
          simp [routingView, routingState, Option.bind_map, Function.comp_def]
        simp only [lists] at *
        rcases ‹routingView _ = initial ∧ _› with ⟨he, hl⟩
        simp_all
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
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => P (routingView w)) (fun _ w => P (routingView w)) :=
    hoare_liftAmbient a _
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => P (routingView w))
        (fun _ w => P (routingView w)) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa only [routingView, hd, Option.map_some, routingState] using hi
  unfold Hoare at ambient skb
  have hl := (indexLookup_routing [.keypair] (u32le msg 4)).wp P
  have hg := fun kp => (keypairGet_routing kp).wp P
  have hp := fun pid => (getPeer_routing pid).wp P
  have he := fun id => (enqueuePerDeviceAndPeerRx_routing id).wp P
  have hqueue := fun id => RetainsRoutingCall.wp (hq id) s
  have hk := fun kp => (keypairPut_routing kp false).wp P
  have hu := fun pid => RetainsRoutingCall.wp (peerPut_retainsRouting pid) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, skb,
    consumeData, newRxSkb, freeRxSkb, hl, hg, hp, he, hqueue, hk, hu,
    keypairGetNull, WG.orM, branch, branchCmp, invariant,
    AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem cpumaskNextOnline_routing : SameView routingView cpumaskNextOnline := by
  apply SameView.of_wp
  intro s
  mvcgen [cpumaskNextOnline, getDev, modifyDev, branch, invariant,
    AmbientM.branch, AmbientM.invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [routingView, routingState]
  all_goals assumption

theorem packetReceive_routing (msg : List UInt8) (src : SkbSource) :
    RetainsRoutingCall (packetReceive msg src) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => P (routingView w)) (fun _ w => P (routingView w)) :=
    hoare_liftAmbient a _
  unfold Hoare at ambient
  have hh := prepareSkbHeader_sameWGWorld msg |>.wp (fun w => P (routingView w))
  have hd := fun protocol bytes => (ipTunnelGetDsfield_sameWGWorld protocol bytes).wp (fun w => P (routingView w))
  have hc := fun ds => RetainsRoutingCall.wp (consumeData_routing msg src ds) s
  have hn := cpumaskNextOnline_routing.wp P
  have hm := (modifyDev_routing (fun d => {d with handshakeQueue := d.handshakeQueue.produce (msg, src), handshakeQueueLen := d.handshakeQueueLen + 1}) (fun _ => rfl)).wp P
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, packetReceive, hh, hd, hc, hn, hm,
    getDev, queueDeviceWork, branch, invariant, unsupported, AmbientM.branch, AmbientM.invariant, AmbientM.unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold routingView at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem wgReceive_routing (msg : List UInt8) (src : SkbSource) :
    RetainsRoutingCall (wgReceive msg src) := by
  apply ProjectedAction.of_wp
  intro s
  have hp := RetainsRoutingCall.wp (packetReceive_routing msg src) s
  mvcgen [wgReceive, hp, branch, unsupported, AmbientM.branch, AmbientM.unsupported]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

end Leanux.Proofs.WG.AllowedIps
