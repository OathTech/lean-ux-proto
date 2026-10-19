import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder

/-! Independent confirmation-order transport through the actual indexed poll.
The replay result and packet come from the current native counter invocation;
packet authentication is supplied separately by the same journal's RX proof. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
open TransportReplay Lifetimes Queues RxJoint
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {E : Type} {recordReplay : TransportDriver.Replay → E} {decode : E → Option ResponderEvent}

abbrev Base (recordReplay : TransportDriver.Replay → E) (decode : E → Option ResponderEvent) :=
  fun h (_ : World) => Safe recordReplay decode h

def Returned (recordReplay : TransportDriver.Replay → E) (decode : E → Option ResponderEvent)
    (pkt : RxPacket) (value : Bool) (h : List E) (_ : World) : Prop :=
  Safe recordReplay decode h ∧ ∃ pre r, h = pre ++ [recordReplay r] ∧ r.packet = pkt ∧ r.run.value = value

private theorem native (action : Leanux.M α) (P : List E → Prop)
    (safe : ∀ h, P h → Safe recordReplay decode h) :
    PrefixEnsures (fun h (_ : World) => P h) (Safe recordReplay decode) (liftPrefix action)
      (fun _ h (_ : World) => P h) :=
  PrefixEnsures.lift action (fun h _ hi => safe h hi) (fun _ _ _ _ hi _ => hi)

private theorem flow_bind (g : PrefixM E α) (f : α → PrefixM E β)
    (hg : PrefixEnsures P S g (fun _ => P)) (hf : ∀ x, PrefixEnsures P S (f x) Q) :
    PrefixEnsures P S (g >>= f) Q := PrefixEnsures.bind hg hf

private theorem stopped (message : String) (f : Unit → PrefixM E α)
    (safe : ∀ h w, P h w → Safe recordReplay decode h) :
    PrefixEnsures P (Safe recordReplay decode) (liftPrefix (liftWG (invariant message)) >>= f) Q := by
  intro w h hi
  exact ⟨[],by simp only [runPrefix_bind,runPrefix_lift,List.append_nil]; rfl,safe h w hi,trivial⟩

private theorem branch_bind (decision : Decision) (value : Bool) (P : List E → Prop)
    (f : Bool → PrefixM E α) (safe : ∀ h, P h → Safe recordReplay decode h)
    (next : ∀ result, result = value → PrefixEnsures (fun h (_ : World) => P h)
      (Safe recordReplay decode) (f result) Q) :
    PrefixEnsures (fun h (_ : World) => P h) (Safe recordReplay decode)
      (liftPrefix (liftWG (branch decision value)) >>= f) Q := by
  apply PrefixEnsures.bind (Q := fun result h (_ : World) => P h ∧ result = value)
  · apply PrefixEnsures.lift _ (fun h _ hi => safe h hi)
    intro h w result v hi run
    cases run
    exact ⟨hi,rfl⟩
  · intro result w h hi
    exact next result hi.2 w h hi.1

private theorem counter (record : TransportDriver.Replay → E) (decode : E → Option ResponderEvent)
    (quiet : ∀ r, Unconfirmed decode (record r)) (skb : SkbId) (pkt : RxPacket) :
    PrefixEnsures (Base record decode) (Safe record decode) (TransportDriver.counter record skb pkt)
      (Returned record decode pkt) := by
  intro w h hi
  rw [TransportDriver.counter_run]
  cases run : (liftWG (counterValidate pkt.keypair pkt.nonce)).run w with
  | error stop => exact ⟨[],by simp,hi,trivial⟩
  | ok out =>
    rcases out with ⟨result,v⟩
    let r : TransportDriver.Replay := ⟨skb,pkt,⟨result,w,v⟩⟩
    have kept := hi.quiet (suffix := [record r]) (by intro event member; obtain rfl := List.mem_singleton.mp member; exact quiet r)
    exact ⟨[record r],rfl,kept,kept,h,r,rfl,rfl,rfl⟩

private theorem cleanup (kp : Option KeypairId) (now : Bool) (f : Unit → PrefixM E α)
    (next : PrefixEnsures (Base recordReplay decode) (Safe recordReplay decode)
      (liftPrefix (liftWG (keypairPut kp now)) >>= f) Q) :
    PrefixEnsures (Returned recordReplay decode pkt result) (Safe recordReplay decode)
      (liftPrefix (liftWG (keypairPut kp now)) >>= f) Q :=
  next.consequence (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)

private theorem consume_bind
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (hc : ∀ pid pkt ep, PrefixEnsures
      (fun h (_ : World) => Safe recordReplay decode h ∧ Accepted recordReplay pid pkt.keypair h)
      (Safe recordReplay decode) (consume pid pkt ep) (fun _ => Base recordReplay decode))
    (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) (result : Bool)
    (accepted : result = true) (peer : pkt.peer = pid)
    (f : Option (List UInt8) → PrefixM E α)
    (next : ∀ x, PrefixEnsures (Base recordReplay decode) (Safe recordReplay decode) (f x) Q) :
    PrefixEnsures (Returned recordReplay decode pkt result) (Safe recordReplay decode)
      (consume pid pkt ep >>= f) Q := by
  apply PrefixEnsures.bind ((hc pid pkt ep).consequence ?_ (fun _ _ _ hi => hi)) next
  intro h w hi
  obtain ⟨safe,pre,r,position,packet,value⟩ := hi
  exact ⟨safe,pre,r,position,packet ▸ peer,by rw [packet],value.trans accepted⟩

open Lean Meta Elab Tactic in
elab "order_contract" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta
  unless target.isAppOf ``PrefixPreserves do throwError "not a preservation contract"
  evalTactic (← `(tactic| apply PrefixEnsures.preserves))

/-- The actual indexed receive loop invokes confirmation only after this packet's
current successful replay check. Stop prefixes keep the ordering proof. -/
theorem poll
    (record : TransportDriver.Replay → E) (decode : E → Option ResponderEvent)
    (quiet : ∀ r, Unconfirmed decode (record r))
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (receive : GroState → List UInt8 → PrefixM E GroState) (flush : GroState → PrefixM E Unit)
    (hc : ∀ pid pkt ep, PrefixEnsures
      (fun h (_ : World) => Safe record decode h ∧ Accepted record pid pkt.keypair h)
      (Safe record decode) (consume pid pkt ep) (fun _ => Base record decode))
    (hr : ∀ gro bytes, PrefixPreserves (Base record decode) (Safe record decode) (receive gro bytes))
    (hf : ∀ gro, PrefixPreserves (Base record decode) (Safe record decode) (flush gro))
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves (Base record decode) (Safe record decode)
      (IndexedPoll.sourceWith (fun a => liftPrefix (liftWG a)) (TransportDriver.counter record)
        consume receive flush pid budget) := by
  unfold IndexedPoll.sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  change PrefixEnsures (Base record decode) (Safe record decode) _ (fun _ => Base record decode)
  repeat' first
    | order_contract
    | (replay_callback consume; apply consume_bind consume hc
       · simp_all
       · simp_all)
    | (replay_callback receive; exact hr _ _)
    | (replay_callback flush; exact hf _)
    | (rx_phase_head plain TransportDriver.counter; apply PrefixEnsures.bind (counter record decode quiet _ _))
    | (replay_native_head invariant; apply stopped; intro h w hi; first | exact hi | exact hi.1)
    | (replay_native_head keypairPut; apply cleanup)
    | (replay_native_head branch; apply branch_bind
       · intro h hi; first | exact hi | exact hi.1
       intro result equal)
    | (replay_head liftPrefix; apply native; intro h hi; first | exact hi | exact hi.1)
    | (replay_head Bind.bind; apply flow_bind)
    | (replay_head ForIn.forIn; apply PrefixPreserves.forIn)
    | (replay_head Pure.pure; apply PrefixEnsures.pure
       · intro h w hi; first | exact hi | exact hi.1
       · intro h w hi; first | exact hi | exact hi.1)
    | (replay_head ite; apply PrefixEnsures.ite)
    | rx_phase_reduce
    | rx_phase_match
    | (rx_phase_intro; try dsimp only)
    | assumption
    | exact fun (h : List E) (w : World) (hi : Base record decode h w) => hi

/-- Native endpoint handling preserves the current accepted replay occurrence
up to the exact confirmation receipt. The consumer tail has an explicit frame. -/
theorem shared_consumer (record : TransportDriver.Replay → E)
    (responder : ResponderEvent → E) (decode : E → Option ResponderEvent)
    (inverse : ∀ event, decode (responder event) = some event)
    (hooks : TransmitSecurity.Driver.Hooks E)
    (confirmed : hooks.confirmation = confirmation responder decode)
    (tail : ∀ pid pkt value, PrefixPreserves (Base record decode) (Safe record decode)
      (liftWGObserver (TransmitSecurity.Driver.receiveTailObserved hooks pid pkt value)))
    (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    PrefixEnsures (fun h (_ : World) => Safe record decode h ∧ Accepted record pid pkt.keypair h)
      (Safe record decode) (liftWGObserver (TransmitSecurity.Driver.consumeObserved hooks pid pkt ep))
      (fun _ => Base record decode) := by
  unfold TransmitSecurity.Driver.consumeObserved
  simp only [liftWGObserver_bind,liftWGObserver_lift,confirmed]
  apply PrefixEnsures.bind (native (liftWG (setPeerEndpoint pid ep))
    (fun h => Safe record decode h ∧ Accepted record pid pkt.keypair h) (fun _ hi => hi.1))
  intro _
  apply PrefixEnsures.bind ((confirmation_checked record responder decode inverse pid pkt.keypair).liftWGObserver)
  intro result
  exact tail pid pkt result

/-- Every confirmation emitted by the actual shared poll has the immediately
preceding successful replay check for the same peer and key. This local caller
contract composes with the same journal's initialized authentication carrier. -/
theorem shared_poll (record : TransportDriver.Replay → E)
    (responder : ResponderEvent → E) (decode : E → Option ResponderEvent)
    (inverse : ∀ event, decode (responder event) = some event)
    (quiet : ∀ r, Unconfirmed decode (record r)) (hooks : TransmitSecurity.Driver.Hooks E)
    (counter : hooks.counterCheck = TransportDriver.counter record)
    (enter : hooks.candidateEnter = fun _ _ => Pure.pure 0)
    (leave : hooks.candidateLeave = fun _ => Pure.pure ())
    (confirmed : hooks.confirmation = confirmation responder decode)
    (tail : ∀ pid pkt value, PrefixPreserves (Base record decode) (Safe record decode)
      (liftWGObserver (TransmitSecurity.Driver.receiveTailObserved hooks pid pkt value)))
    (toStack : List (List UInt8) → PrefixM E Unit)
    (receive : ∀ gro bytes, PrefixPreserves (Base record decode) (Safe record decode)
      (napiGroReceivePrefix toStack gro bytes))
    (flush : ∀ gro, PrefixPreserves (Base record decode) (Safe record decode)
      (napiGroFlushAllPrefix toStack gro)) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (Base record decode) (Safe record decode)
      (TransmitSecurity.Driver.pollObserved hooks pid budget toStack) := by
  unfold TransmitSecurity.Driver.pollObserved
  simp only [liftWGObserver_lift,counter,enter,leave,CandidatePoll.neutral]
  exact poll record decode quiet _ _ _
    (shared_consumer record responder decode inverse hooks confirmed tail) receive flush pid budget

end Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder
