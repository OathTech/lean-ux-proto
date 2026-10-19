import Leanux.Proofs.WG.Noise.CounterConsumeFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.CounterConsume
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes RxJoint
variable {α β : Type}

def counterBlock (pid n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    Obs (Option (Option Entry)) := do
  let b ← receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
    (Event.checkedCounter n id stamp pkt)
  if !(← liftPrefix (branch .rxPollCounterInvalid !b)) then
    let ep ← receiptObserved (liftPrefix (liftWG (endpointFromSkb pkt.source)))
      (Event.checkedEndpoint n id stamp pkt)
    if !(← liftPrefix (branch .rxPollEndpointFailed ep.isNone)) then
      let some endpoint := ep | liftPrefix (invariant "unreachable")
      let out ← consume pid n id stamp pkt endpoint
      return some out
  return none

theorem counterBlock_checked (pid n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (fun h _ => Checks h) Checks (counterBlock pid n id stamp pkt) := by
  apply PrefixEnsures.preserves
  unfold counterBlock
  apply PrefixEnsures.bind (counter_observed n id stamp pkt)
  intro b
  apply branch_const
  · intro h w v same hi
    exact ⟨hi.1,same ▸ hi.2⟩
  cases b with
  | false =>
    exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi.1)
  | true =>
    simp only [Bool.not_true,Bool.not_false,ite_true]
    apply PrefixEnsures.bind (endpoint_anchored n id stamp pkt true)
    intro ep
    apply branch_const
    · intro h w v same hi
      exact ⟨hi.1,same ▸ hi.2⟩
    cases ep with
    | none => exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi.1)
    | some endpoint =>
      simp only [Option.isNone_some,Bool.not_false,ite_true]
      apply PrefixEnsures.bind (consume_checked pid n id stamp pkt endpoint)
      intro out
      exact PrefixEnsures.pure (fun _ _ hi => hi) (fun _ _ hi => hi)


def pollWithBlock (pid : PeerId) (budget : Nat) : Obs Nat := do
  if ← liftPrefix (branch .rxPollNoBudget (budget == 0)) then return 0
  let mut workDone := 0
  let mut gro : Gro := {}
  let mut drained := false
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    let first ← access (liftWGObserver (peekAccess pid))
    let go ← access (liftWGObserver (readyAccess first))
    if !go then
      drained := true
      break
    let some id := first | liftPrefix (invariant "unreachable")
    let captured ← capture id
    let pkt := captured.1
    if pkt.peer != pid then liftPrefix (invariant "a packet on another peer's rx_queue")
    drop pid workDone id captured.2
    let mut free := true
    if !(← receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (Event.checkedState workDone id captured.2 pkt)) then
      match ← counterBlock pid workDone id captured.2 pkt with
      | none => pure ()
      | some returned =>
        for entry in returned.toList do
          gro ← receive gro entry
        free := false
    access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
    access (liftWGObserver (peerPutMixed (some pid)))
    _ ← liftPrefix (branch .rxPollFree free)
    access (liftWGObserver (freeRxSkbPrefix id))
    workDone := workDone + 1
    if ← liftPrefix (branch .rxPollBudgetDone (workDone ≥ budget)) then break
  if !drained && workDone < budget then liftPrefix (invariant "the rx_queue did not drain")
  if ← liftPrefix (branch .rxPollComplete (workDone < budget)) then
    access (liftWGObserver (completeAccess pid))
    flushAll gro
  else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
  return workDone


theorem stop_bind (why : String) (f : α → Obs β) :
    (liftPrefix (invariant why) >>= f) = liftPrefix (invariant why) := by
  funext w
  rfl

theorem counterBlock_bind (pid n id : Nat) (stamp : PacketStamp) (pkt : RxPacket)
    (f : Option (Option Entry) → Obs α) :
    (counterBlock pid n id stamp pkt >>= f) = (do
      let b ← receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
        (Event.checkedCounter n id stamp pkt)
      if !(← liftPrefix (branch .rxPollCounterInvalid !b)) then
        let ep ← receiptObserved (liftPrefix (liftWG (endpointFromSkb pkt.source)))
          (Event.checkedEndpoint n id stamp pkt)
        if !(← liftPrefix (branch .rxPollEndpointFailed ep.isNone)) then
          let some endpoint := ep | liftPrefix (invariant "unreachable")
          let out ← consume pid n id stamp pkt endpoint
          f (some out)
        else f none
      else f none) := by
  simp only [counterBlock,bind_assoc,pure_bind,RxCredits.bind_if_source]
  congr 1
  funext b
  congr 1
  funext rejected
  split <;> try rfl
  congr 1
  funext ep
  congr 1
  funext failed
  split <;> try rfl
  cases ep <;> simp only [stop_bind,bind_assoc,pure_bind]

theorem poll_factor (pid : PeerId) (budget : Nat) :
    RxJoint.poll pid budget = pollWithBlock pid budget := by
  simp only [RxJoint.poll,pollWithBlock,counterBlock_bind,stop_bind]
  rfl

theorem capture_checks (id : SkbId) :
    PrefixPreserves (fun h _ => Checks h) Checks (capture id) := by
  intro w h hi
  obtain ⟨s,he,hs,hn⟩ := access_checks (liftWGObserver (getRxSkbPrefix id)) w h hi
  refine ⟨s,he,hs,?_⟩
  cases (runPrefix (capture id) w h).1 <;> trivial

theorem drop_checks (pid n id : Nat) (stamp : PacketStamp) :
    PrefixPreserves (fun h _ => Checks h) Checks (drop pid n id stamp) := by
  unfold drop
  exact (access_checks _).bind (fun _ => emit_checks _ (fun _ => True.intro))

theorem receive_checks (g : Gro) (e : Entry) :
    PrefixPreserves (fun h _ => Checks h) Checks (receive g e) := by
  rw [GroSource.receive_factor]
  apply GroSource.receive_preserves (I := fun h (_ : World) => Checks h) (S := Checks) _root_.id _ (fun _ _ hi => hi)
  · intro e h w hi
    exact checks_snoc hi True.intro
  · intro bytes
    exact access_checks _
  · intro e w h x v t hi run next
    exact checks_snoc next True.intro

theorem flushAll_checks (g : Gro) :
    PrefixPreserves (fun h _ => Checks h) Checks (flushAll g) := by
  rw [GroSource.flushAll_factor]
  apply GroSource.flushAll_preserves (I := fun h (_ : World) => Checks h) (S := Checks) _root_.id _ (fun _ _ hi => hi)
  · intro e h w hi
    exact checks_snoc hi True.intro
  · intro bytes
    exact access_checks _
  · intro e w h x v t hi run next
    exact checks_snoc next True.intro


theorem state_checks (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (fun h _ => Checks h) Checks
      (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (Event.checkedState n id stamp pkt)) :=
  receipt_checks _ _ (lift_checks _) (fun _ _ => True.intro)

theorem checks_bind (a : Obs α) (f : α → Obs β)
    (ha : PrefixPreserves (fun h _ => Checks h) Checks a)
    (hf : ∀ x, PrefixPreserves (fun h _ => Checks h) Checks (f x)) :
    PrefixPreserves (fun h _ => Checks h) Checks (a >>= f) := ha.bind hf

/-- The existing owned poll factor now carries its actual capture until the
CRYPTED branch. No new observer or account traversal is introduced. -/
theorem poll_preserves_selected
    (I : List Event → World → Prop) (S : List Event → Prop)
    (Selected : SkbId → PacketStamp → RxPacket → List Event → World → Prop)
    (safe : ∀ h w, I h w → S h)
    (forget : ∀ id stamp pkt h w, Selected id stamp pkt h w → I h w)
    (peek : ∀ pid, PrefixPreserves I S (access (liftWGObserver (peekAccess pid))))
    (ready : ∀ first, PrefixPreserves I S (access (liftWGObserver (readyAccess first))))
    (captured : ∀ id, PrefixEnsures I S (capture id)
      (fun out => Selected id out.2 out.1))
    (dropped : ∀ pid n id stamp pkt,
      PrefixPreserves (Selected id stamp pkt) S (drop pid n id stamp))
    (state : ∀ n id stamp pkt,
      PrefixEnsures (Selected id stamp pkt) S
        (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
          (Event.checkedState n id stamp pkt))
        (fun b h w => Selected id stamp pkt h w ∧ b = (pkt.state != .crypted)))
    (block : ∀ pid n id stamp pkt, pkt.state = .crypted →
      PrefixEnsures (Selected id stamp pkt) S (counterBlock pid n id stamp pkt)
        (fun _ => I))
    (keypair : ∀ id, PrefixPreserves I S
      (access (liftWGObserver (keypairPutPrefix (some id) false))))
    (peer : ∀ pid, PrefixPreserves I S
      (access (liftWGObserver (peerPutMixed (some pid)))))
    (free : ∀ id, PrefixPreserves I S (access (liftWGObserver (freeRxSkbPrefix id))))
    (complete : ∀ pid, PrefixPreserves I S (access (liftWGObserver (completeAccess pid))))
    (ambient : ∀ site value, PrefixPreserves I S (liftPrefix (branch site value)))
    (received : ∀ g e, PrefixPreserves I S (receive g e))
    (flushed : ∀ g, PrefixPreserves I S (flushAll g))
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves I S (RxJoint.poll pid budget) := by
  have keepBind {α β : Type} (a : Obs α) (f : α → Obs β)
      (ha : PrefixPreserves I S a)
      (hf : ∀ x, PrefixEnsures I S (f x) (fun _ => I)) :
      PrefixEnsures I S (a >>= f) (fun _ => I) := PrefixEnsures.bind ha hf
  have selectedBind {α β : Type} {id : SkbId} {stamp : PacketStamp} {pkt : RxPacket}
      (a : Obs α) (f : α → Obs β)
      (ha : PrefixPreserves (Selected id stamp pkt) S a)
      (hf : ∀ x, PrefixEnsures (Selected id stamp pkt) S (f x) (fun _ => I)) :
      PrefixEnsures (Selected id stamp pkt) S (a >>= f) (fun _ => I) := PrefixEnsures.bind ha hf
  have forgetBind {α β : Type} {id : SkbId} {stamp : PacketStamp} {pkt : RxPacket}
      (a : Obs α) (f : α → Obs β)
      (ha : PrefixPreserves I S a)
      (hf : ∀ x, PrefixEnsures I S (f x) (fun _ => I)) :
      PrefixEnsures (Selected id stamp pkt) S (a >>= f) (fun _ => I) :=
    PrefixEnsures.consequence (PrefixEnsures.bind ha hf) (forget id stamp pkt) (fun _ _ _ hi => hi)
  have stateBind {β : Type} (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket)
      (f : Bool → Obs β)
      (hf : ∀ b, b = (pkt.state != .crypted) →
        PrefixEnsures (Selected id stamp pkt) S (f b) (fun _ => I)) :
      PrefixEnsures (Selected id stamp pkt) S
        (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
          (Event.checkedState n id stamp pkt) >>= f) (fun _ => I) := by
    apply PrefixEnsures.bind (state n id stamp pkt)
    intro b w h hi
    exact hf b hi.2 w h hi.1
  have stopped {α β : Type} {P : List Event → World → Prop}
      (why : String) (f : α → Obs β) (hs : ∀h w,P h w→S h) :
      PrefixEnsures P S (liftPrefix (invariant why) >>= f) (fun _=>I) := by
    intro w h hi
    exact ⟨[],by change h = h ++ []; simp,hs h w hi,True.intro⟩
  have crypted {pkt : RxPacket} (eq : false = (pkt.state != .crypted)) :
      pkt.state = .crypted := by
    generalize pkt.state = s at eq ⊢
    cases s <;> first | rfl | cases eq
  rw [poll_factor]
  unfold pollWithBlock
  apply PrefixEnsures.preserves
  repeat' first
    | rx_phase_reduce
    | (rx_phase_head plain Pure.pure
       first
       | exact PrefixEnsures.pure safe (fun _ _ hi=>hi)
       | exact PrefixEnsures.pure (fun h w hi=>safe h w (forget _ _ _ h w hi))
           (forget _ _ _))
    | (rx_phase_head plain counterBlock
       apply PrefixEnsures.bind (block _ _ _ _ _ (crypted (by assumption))))
    | (rx_phase_head plain capture; apply PrefixEnsures.bind (captured _))
    | (rx_phase_head plain drop; apply selectedBind _ _ (dropped _ _ _ _ _))
    | (rx_phase_head receipt branch
       apply stateBind
       intro b eq
       cases b <;> simp only [Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_true,ite_false])
    | (rx_phase_head plain invariant
       apply stopped
       first
       | exact safe
       | exact fun h w hi=>safe h w (forget _ _ _ h w hi))
    | (rx_phase_head plain unsupported
       intro w h hi
       exact ⟨[],by change h = h ++ []; simp,safe h w hi,True.intro⟩)
    | (rx_phase_head plain peekAccess; apply keepBind _ _ (peek _))
    | (rx_phase_head plain readyAccess; apply keepBind _ _ (ready _))
    | (rx_phase_head plain keypairPutPrefix; first
       | apply keepBind _ _ (keypair _)
       | apply forgetBind _ _ (keypair _))
    | (rx_phase_head plain peerPutMixed; apply keepBind _ _ (peer _))
    | (rx_phase_head plain freeRxSkbPrefix; apply keepBind _ _ (free _))
    | (rx_phase_head plain completeAccess; apply keepBind _ _ (complete _))
    | (rx_phase_head plain receive; apply keepBind _ _ (received _ _))
    | (rx_phase_head plain flushAll; apply keepBind _ _ (flushed _))
    | (rx_phase_head plain branch; apply keepBind _ _ (ambient _ _))
    | (rx_phase_head plain ForIn.forIn; apply keepBind _ _; first
       | apply PrefixPreserves.range
       | apply PrefixPreserves.forIn)
    | (rx_phase_head plain ite; apply PrefixEnsures.ite)
    | exact safe
    | rx_phase_intro
    | rx_phase_match

theorem poll_checks (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun h _ => Checks h) Checks (RxJoint.poll pid budget) := by
  apply poll_preserves_selected (fun h _=>Checks h) Checks
    (fun _ _ _ h _=>Checks h) (fun _ _ hi=>hi) (fun _ _ _ _ _ hi=>hi)
  · intro p; exact access_checks _
  · intro first; exact access_checks _
  · exact capture_checks
  · intro p n id stamp pkt; exact drop_checks p n id stamp
  · intro n id stamp pkt w h hi
    have checked := state_checks n id stamp pkt w h hi
    rcases checked with ⟨suffix,append,safe,normal⟩
    refine ⟨suffix,append,safe,?_⟩
    change Checks _ ∧ (pkt.state != .crypted) = (pkt.state != .crypted)
    exact ⟨normal,rfl⟩
  · intro p n id stamp pkt _; exact counterBlock_checked p n id stamp pkt
  · intro id; exact access_checks _
  · intro p; exact access_checks _
  · intro id; exact access_checks _
  · intro p; exact access_checks _
  · intro site b; exact lift_checks _
  · exact receive_checks
  · exact flushAll_checks

theorem checks_append {h t : List Event} (left : Checks h) (right : Checks t) :
    Checks (h ++ t) := by
  intro e member
  rcases List.mem_append.mp member with member | member
  · exact support_mono (left e member) (List.sublist_append_left _ _)
  · exact support_mono (right e member) (List.sublist_append_right _ _)

theorem checks_seed (prior : List LifetimeEvent) : Checks (seed prior) := by
  intro e member
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp member
  trivial

theorem checks_suffix (prior : List LifetimeEvent) (suffix : List Event)
    (checked : Checks (seed prior ++ suffix)) : Checks suffix := by
  intro e member
  cases e with
  | consumed n id stamp r =>
    obtain ⟨cr,present,valid,value,device⟩ :=
      checked (.consumed n id stamp r) (List.mem_append_right _ member)
    rcases List.mem_append.mp present with present | present
    · have absent : Event.checkedCounter n id stamp r.packet cr ∉ seed prior := by
        simp [seed]
      exact False.elim (absent present)
    · exact ⟨cr,present,valid,value,device⟩
  | _ => trivial

def HistoryChecks (h : List RxHistory.Event) : Prop := Checks (h.filterMap RxLink.historyEvent)

theorem observePoll_checks (pid : PeerId) (budget : Nat) :
    RxLink.Preserves HistoryChecks (RxHistory.observePoll pid budget) := by
  intro w h hi
  obtain ⟨suffix,append⟩ := RxJoint.poll_appends pid budget w (seed (RxHistory.prior h))
  have whole := (poll_checks pid budget w (seed (RxHistory.prior h))
    (checks_seed (RxHistory.prior h))).choose_spec.2.1
  rw [append] at whole
  have suffixChecked := checks_suffix (RxHistory.prior h) suffix whole
  have run := RxHistory.observePoll_suffix pid budget w h _ suffix (Prod.ext rfl append)
  have checked : HistoryChecks (h ++ suffix.map RxHistory.promote) := by
    unfold HistoryChecks
    rw [List.filterMap_append,RxLink.promote_history]
    exact checks_append hi suffixChecked
  refine ⟨suffix.map RxHistory.promote,by rw [run],by simpa only [run] using checked,?_⟩
  rw [run]
  cases (runPrefix (RxJoint.poll pid budget) w (seed (RxHistory.prior h))).1 <;> trivial

theorem audit_checks (a : AuditM α) : RxLink.Preserves HistoryChecks (RxHistory.audit a) := by
  apply RxLink.audit_from_suffix
  intro h s hi
  unfold HistoryChecks at hi ⊢
  rw [List.filterMap_append]
  apply checks_append_quiet hi
  intro e he pre
  obtain ⟨x,hx,he⟩ := List.mem_filterMap.mp he
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hx
  cases x <;> simp only [RxLink.historyEvent,Option.some.injEq,reduceCtorEq] at he
  subst e
  trivial

theorem origin_checks (a : PrefixM Origins.Event α) :
    RxLink.Preserves HistoryChecks (Origins.HistoryAdapters.focus a) := by
  apply Origins.HistoryAdapters.focus_history
  intro h s hi
  unfold HistoryChecks at hi ⊢
  rw [List.filterMap_append]
  apply checks_append_quiet hi
  intro e he pre
  obtain ⟨x,hx,he⟩ := List.mem_filterMap.mp he
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hx
  cases x <;> simp only [Origins.HistoryAdapters.encode,RxLink.historyEvent,
    Option.some.injEq,reduceCtorEq] at he
  subst e
  trivial

instance counterProtocol : RxLink.Protocol HistoryChecks :=
  ⟨audit_checks,observePoll_checks,fun a _ => origin_checks a⟩

theorem initialized_checks (trace : Runner.Trace) (placeholders : Bool) :
    HistoryChecks (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 :=
  RxLink.executeTraceHistory_protocol trace placeholders (by intro e member; cases member)

theorem initialized_counter_cut (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (n id : Nat) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed n id stamp r :: post) :
    CounterAt n id stamp r.packet true
      ((runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2.filterMap RxLink.historyEvent)
      r.run.before.dev := by
  apply initialized_checks trace placeholders (.consumed n id stamp r)
  apply List.mem_filterMap.mpr
  refine ⟨.consumed n id stamp r,?_,rfl⟩
  rw [position]
  simp

theorem initialized_consumed_stamp (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (n id : Nat) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed n id stamp r :: post) :
    ∃ allocation, ConsumeConfirmation.keyStampAt r.run.before r.packet.keypair = some allocation := by
  obtain ⟨cr,member,valid,value,device⟩ :=
    initialized_counter_cut trace placeholders pre post n id stamp r position
  obtain ⟨allocation,before,after⟩ := counter_product_stamp r.packet cr valid
  refine ⟨allocation,?_⟩
  simpa only [ConsumeConfirmation.keyStampAt,device] using after



end Leanux.Proofs.WG.Noise.CounterConsume
