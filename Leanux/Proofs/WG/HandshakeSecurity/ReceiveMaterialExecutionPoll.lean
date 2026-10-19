import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialExecutionPollBase

/-! The native indexed poll carries allocation identity and confirmation
certificates jointly, preserving receipts even when its consumer later stops. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues RxJoint AuthenticatedEffects TransmitSecurity
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option pp.structureInstances false
variable {pkt : RxPacket} {result : Bool} {skb : SkbId}

private theorem base_pure (x : α) : PrefixPreserves Base Safe (pure x) :=
  PrefixPreserves.pure (fun _ _ hi => hi.safe) x

private theorem flow_bind (g : PrefixM Journal.Event α) (f : α → PrefixM Journal.Event β)
    (hg : PrefixPreserves P Safe g) (hf : ∀ x, PrefixEnsures P Safe (f x) Q) :
    PrefixEnsures P Safe (g >>= f) Q := PrefixEnsures.bind hg hf

private theorem read_bind (id : SkbId) (f : RxPacket → PrefixM Journal.Event α)
    (hf : ∀ packet, PrefixEnsures (Picked id packet) Safe (f packet) Q) :
    PrefixEnsures Base Safe (liftPrefix (liftWG (getRxSkb id)) >>= f) Q :=
  PrefixEnsures.bind (read_selected id) hf

private theorem picked_cleanup (kp : Option KeypairId) (now : Bool) (f : Unit → PrefixM Journal.Event α)
    (hf : PrefixEnsures Base Safe (liftPrefix (liftWG (keypairPut kp now)) >>= f) Q) :
    PrefixEnsures (Picked skb pkt) Safe (liftPrefix (liftWG (keypairPut kp now)) >>= f) Q :=
  hf.consequence (fun _ _ hi => ⟨hi.1.1,hi.2⟩) (fun _ _ _ hi => hi)

private theorem counter_cleanup (kp : Option KeypairId) (now : Bool) (f : Unit → PrefixM Journal.Event α)
    (hf : PrefixEnsures Base Safe (liftPrefix (liftWG (keypairPut kp now)) >>= f) Q) :
    PrefixEnsures (AtCounter pkt result) Safe (liftPrefix (liftWG (keypairPut kp now)) >>= f) Q :=
  hf.consequence (fun _ _ hi => ⟨hi.1.1,hi.2⟩) (fun _ _ _ hi => hi)

private theorem stop (message : String) (f : Unit → PrefixM Journal.Event α)
    (safe : ∀ h w, P h w → Safe h) :
    PrefixEnsures P Safe (liftPrefix (liftWG (invariant message)) >>= f) Q := by
  intro w h hi
  exact ⟨[],by simp only [runPrefix_bind,runPrefix_lift,List.append_nil]; rfl,safe h w hi,trivial⟩

private theorem branch_bind (decision : Decision) (value : Bool) (f : Bool → PrefixM Journal.Event α)
    (safe : ∀ h w, P h w → Safe h)
    (frame : ∀ h w v, w.wg = v.wg → P h w → P h v)
    (next : ∀ result, result = value → PrefixEnsures P Safe (f result) Q) :
    PrefixEnsures P Safe (liftPrefix (liftWG (branch decision value)) >>= f) Q := by
  apply PrefixEnsures.bind (Q := fun result h w => P h w ∧ result = value)
  · apply PrefixEnsures.lift _ safe
    intro h w result v hi run
    cases run
    exact ⟨frame h w _ rfl hi,rfl⟩
  · intro result w h hi
    exact next result hi.2 w h hi.1

private theorem consume_bind
    (consume : PeerId → RxPacket → Endpoint → PrefixM Journal.Event (Option (List UInt8)))
    (hc : ∀ pid pkt ep, pkt.peer = pid → PrefixEnsures (AtCounter pkt true) Safe
      (consume pid pkt ep) (fun _ => Base))
    (pid : PeerId) (ep : Endpoint) (f : Option (List UInt8) → PrefixM Journal.Event α)
    (accepted : result = true) (peer : pkt.peer = pid)
    (next : ∀ x, PrefixEnsures Base Safe (f x) Q) :
    PrefixEnsures (AtCounter pkt result) Safe (consume pid pkt ep >>= f) Q := by
  subst result
  exact PrefixEnsures.bind (hc pid pkt ep peer) next

macro "receive_execution_safe" : tactic => `(tactic| (
  intro h w hi
  first | exact Base.safe hi | exact Picked.safe hi | exact AtCounter.safe hi))

macro "receive_execution_poll_step" : tactic => `(tactic| first
  | replay_contract
  | rx_phase_reduce
  | (replay_native_head invariant; apply stop; receive_execution_safe)
  | (replay_native_head getRxSkb; apply read_bind)
  | (replay_native_head keypairPut; first | apply picked_cleanup | apply counter_cleanup)
  | (replay_native_head branch; apply branch_bind
     · receive_execution_safe
     · intro h w v same hi
       first | exact Base.wg same hi | exact Picked.wg same hi | exact AtCounter.wg same hi
     intro result equal)
  | (replay_head Pure.pure; exact base_pure _)
  | (replay_head ite; apply PrefixEnsures.ite)
  | rx_phase_match)

theorem poll_authorized
    (consume : PeerId → RxPacket → Endpoint → PrefixM Journal.Event (Option (List UInt8)))
    (receive : GroState → List UInt8 → PrefixM Journal.Event GroState)
    (flush : GroState → PrefixM Journal.Event Unit)
    (hc : ∀ pid pkt ep, pkt.peer = pid → PrefixEnsures (AtCounter pkt true) Safe
      (consume pid pkt ep) (fun _ => Base))
    (hr : ∀ gro bytes, PrefixPreserves Base Safe (receive gro bytes))
    (hf : ∀ gro, PrefixPreserves Base Safe (flush gro))
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves Base Safe
      (IndexedPoll.sourceWith (fun a => liftPrefix (liftWG a)) (TransportDriver.counter Journal.Event.replay)
        consume receive flush pid budget) := by
  unfold IndexedPoll.sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  change PrefixEnsures Base Safe _ (fun _ => Base)
  repeat' first
    | (replay_callback consume; apply consume_bind consume hc
       · simp_all
       · simp_all)
    | (replay_callback receive; with_reducible exact hr _ _)
    | (replay_callback flush; with_reducible exact hf _)
    | (rx_phase_head plain TransportDriver.counter
       with_reducible apply PrefixEnsures.bind (counter_returned _ _
        (by apply Replay.crypted_of_test; simp_all)))
    | receive_execution_poll_step
    | (replay_head liftPrefix
       first
       | solve | apply poll_native
         · intro h; receive_material_native_frame
         · receive_material_bounds_frame
       | solve | apply picked_native
         · replay_native_frame
         · intro h; receive_material_native_frame
         · receive_material_bounds_frame
       | solve | apply atCounter_native
         · replay_native_frame
         · intro h; receive_material_native_frame
         · receive_material_bounds_frame)
    | (replay_head Bind.bind; apply flow_bind)
    | (replay_head ForIn.forIn; apply PrefixPreserves.forIn)
    | exact fun (h : List Journal.Event) (w : World) (hi : Base h w) => hi.safe
    | (rx_phase_intro; try dsimp only)
  all_goals first
    | exact hr _ _
    | exact hf _
    | (apply picked_native
       · replay_native_frame
       · intro h; receive_material_native_frame
       · receive_material_bounds_frame)
    | (apply atCounter_native
       · replay_native_frame
       · intro h; receive_material_native_frame
       · receive_material_bounds_frame)
    | (apply poll_native
       · intro h; receive_material_native_frame
       · receive_material_bounds_frame)

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
