import Leanux.Proofs.WG.Queues.RxPollCompletion

/-! Consume receipts are checked independently of the old allocation and
completion invariants. The journal starts fresh, and GRO carries the actual
Some receipt with its payload even after packet storage is released. -/
namespace Leanux.Proofs.WG.Queues.RxDisposition
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes RxJoint Std.Do

/-- The complete RX-store view needed between capture and consume; queue-only
frames do not establish this field-level relation. -/
def rxStore (w : World) :=
  (w.k.wg.map (fun d => d.ifindex), fun id : SkbId => w.k.wg.bind (fun d => d.rxSkbs[id]?))

def SelectedAt (skb : SkbId) (stamp : PacketStamp) (pkt : RxPacket) (w : World) : Prop :=
  packetStamp w skb = stamp ∧ (rxStore w).2 skb = some pkt

theorem capture_selected (skb : SkbId) (w v : World) (h : List RxJoint.Event)
    (pkt : RxPacket) (stamp : PacketStamp)
    (hr : (runPrefix (capture skb) w h).1 = .ok ((pkt, stamp), v)) :
    v = w ∧ SelectedAt skb stamp pkt v := by
  rw [capture_run] at hr
  cases hg : (getRxSkb skb).run w with
  | error e => simp [hg] at hr
  | ok out =>
    rcases out with ⟨p, u⟩
    simp only [hg, Except.ok.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    obtain ⟨rfl, d, hd, hp⟩ := Packets.getRxSkb_current skb w u p hg
    exact ⟨rfl, rfl, by simp [rxStore, hd, hp]⟩

theorem drop_rxStore (pid : PeerId) : SameView rxStore
    (do setPeer pid {(← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.dropPeeked}) := by
  apply SameView.of_wp
  intro s
  mvcgen [getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold rxStore at *; simp_all only [Option.bind_some, Option.bind_map, Option.map_map, Option.map_some, Function.comp_def]

theorem counter_rxStore (kp : KeypairId) (nonce : Nat) :
    SameView rxStore (counterValidate kp nonce) := by
  apply SameView.of_wp
  intro s
  mvcgen [counterValidate, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    branch, branchCmp, WG.orM, invariant]
  all_goals try exact ((⇓? _ w => ⌜rxStore w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try unfold rxStore at *; simp_all only [Option.bind_some, Option.bind_map, Option.map_map, Option.map_some, Function.comp_def]
  all_goals trivial

theorem selected_transport (skb : SkbId) (stamp : PacketStamp) (pkt : RxPacket)
    (w v : World) (he : rxStore v = rxStore w) (hi : SelectedAt skb stamp pkt w) :
    SelectedAt skb stamp pkt v := by
  refine ⟨?_, by simpa only [he] using hi.2⟩
  have hs := congrArg Prod.fst he
  have hp : packetStamp v skb = packetStamp w skb := by
    simpa only [rxStore, packetStamp] using congrArg (fun o : Option Nat => (o.getD 0, skb + 1)) hs
  exact hp.trans hi.1

/-- Validity of the actual consume run and its Some payload only. This does
not yet link the receipt packet/peer to the earlier captured skb and stamp.
Plain optional metadata does not imply validity for arbitrary entries. -/
def ConsumePayloadValid (e : Entry) : Prop :=
  ∃ r, e.origin = some r ∧ r.Valid ∧ r.run.value = some e.tag.bytes

def EventValid : RxJoint.Event → Prop
  | .checkedState _ _ _ pkt r => r.Valid (branch .rxPollNotCrypted (pkt.state != .crypted))
  | .checkedCounter _ _ _ pkt r => r.Valid (counterValidate pkt.keypair pkt.nonce)
  | .checkedEndpoint _ _ _ pkt r => r.Valid (endpointFromSkb pkt.source)
  | .consumed _ _ _ r => r.Valid
  | .buffered e | .entered e | .completed e _ => ConsumePayloadValid e
  | _ => True

def Valid (h : List RxJoint.Event) : Prop := ∀ e ∈ h, EventValid e

theorem valid_append (h t : List RxJoint.Event) :
    Valid (h ++ t) ↔ Valid h ∧ Valid t := by
  simp only [Valid, List.mem_append, or_imp, forall_and]

theorem valid_emit (e : RxJoint.Event) (he : EventValid e) :
    PrefixPreserves (fun h _ => Valid h) Valid (emitPrefix e) := by
  intro w h hi
  have hv : Valid (h ++ [e]) := valid_append h [e] |>.mpr ⟨hi, by simpa [Valid] using he⟩
  exact ⟨[e], rfl, hv, hv⟩

theorem valid_access (a : MixedM α) :
    PrefixPreserves (fun h _ => Valid h) Valid (access a) := by
  intro w h hi
  let suffix := ((runPrefix a w (h.filterMap accessEvent)).2.drop
    (h.filterMap accessEvent).length).map RxJoint.Event.access
  have hv : Valid (h ++ suffix) := by
    apply (valid_append _ _).mpr
    refine ⟨hi, ?_⟩
    intro e he
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp he
    trivial
  refine ⟨suffix, rfl, hv, ?_⟩
  cases (runPrefix (access a) w h).1 <;> trivial

theorem valid_lift (a : M α) :
    PrefixPreserves (fun h _ => Valid h) Valid (liftPrefix a) :=
  by
    intro w h hi
    refine ⟨[], by simp, hi, ?_⟩
    simp only [runPrefix_lift]
    cases a.run w <;> trivial

theorem valid_receipt (a : Obs α) (original : M α) (f : RunWitness α → RxJoint.Event)
    (ha : PrefixPreserves (fun h _ => Valid h) Valid a) (he : ErasesPrefix a original)
    (hf : ∀ r, r.Valid original → EventValid (f r)) :
    PrefixPreserves (fun h _ => Valid h) Valid (receiptObserved a f) := by
  intro w h hi
  obtain ⟨s, hs, hv, _⟩ := ha w h hi
  have ho := he w h
  rw [runPrefix_receiptObserved]
  cases hr : runPrefix a w h with
  | mk result t =>
    simp only [hr] at hs hv ho
    cases result with
    | error e => exact ⟨s, hs, hv, True.intro⟩
    | ok out =>
      rcases out with ⟨x, v⟩
      have hg : Valid (t ++ [f ⟨x, w, v⟩]) :=
        (valid_append _ _).mpr ⟨hv, by simpa [Valid] using hf ⟨x, w, v⟩ ho.symm⟩
      exact ⟨s ++ [f ⟨x, w, v⟩], by simp only [hs, List.append_assoc], hg, hg⟩

theorem valid_state (n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (fun h _ => Valid h) Valid
      (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (RxJoint.Event.checkedState n skb stamp pkt)) :=
  valid_receipt _ _ _ (valid_lift _) (erasesPrefix_lift _) (fun _ hv => hv)

theorem valid_counter (n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (fun h _ => Valid h) Valid
      (receiptObserved (access (counterValidatePrefix pkt.keypair pkt.nonce))
        (RxJoint.Event.checkedCounter n skb stamp pkt)) :=
  valid_receipt _ _ _ (valid_access _) (access_erases (counterValidatePrefix_erases _ _)) (fun _ hv => hv)

theorem valid_endpoint (n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (fun h _ => Valid h) Valid
      (receiptObserved (liftPrefix (endpointFromSkb pkt.source))
        (RxJoint.Event.checkedEndpoint n skb stamp pkt)) :=
  valid_receipt _ _ _ (valid_lift _) (erasesPrefix_lift _) (fun _ hv => hv)

theorem valid_capture (skb : SkbId) :
    PrefixPreserves (fun h _ => Valid h) Valid (capture skb) := by
  intro w h hi
  obtain ⟨s, he, hs, hn⟩ := valid_access (getRxSkbPrefix skb) w h hi
  refine ⟨s, he, hs, ?_⟩
  cases (runPrefix (capture skb) w h).1 <;> trivial

theorem valid_drop (pid n skb : Nat) (stamp : PacketStamp) :
    PrefixPreserves (fun h _ => Valid h) Valid (drop pid n skb stamp) :=
  (valid_access _).bind (fun _ => valid_emit _ True.intro)

theorem valid_consume (pid n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    PrefixEnsures (fun h _ => Valid h) Valid (consume pid n skb stamp pkt ep)
      (fun out h _ => Valid h ∧ ∀ e ∈ out.toList, ConsumePayloadValid e) := by
  intro w h hi
  obtain ⟨s, hs, hv, _⟩ := valid_access (consumeDataDonePrefix pid pkt ep) w h hi
  have he := access_erases (consumeDataDonePrefix_erases pid pkt ep) w h
  rw [consume_run]
  cases hr : runPrefix (access (consumeDataDonePrefix pid pkt ep)) w h with
  | mk result t =>
    simp only [hr] at hs hv he
    cases result with
    | error err => exact ⟨s, hs, hv, True.intro⟩
    | ok out =>
      rcases out with ⟨out, v⟩
      let r : ConsumeReceipt := ⟨pid, pkt, ep, ⟨out, w, v⟩⟩
      have rv : r.Valid := he.symm
      have hc : Valid (t ++ [.consumed n skb stamp r]) :=
        (valid_append _ _).mpr ⟨hv, by simpa [Valid, EventValid] using rv⟩
      cases out with
      | none => exact ⟨s ++ [.consumed n skb stamp r], by simp only [hs, List.append_assoc]; rfl, hc, hc, by simp⟩
      | some bytes =>
        let e : Entry := ⟨⟨n, skb, bytes⟩, stamp, some r⟩
        have ev : ConsumePayloadValid e := ⟨r, rfl, rv, rfl⟩
        have hb : Valid ((t ++ [.consumed n skb stamp r]) ++ [.buffered e]) :=
          (valid_append _ _).mpr ⟨hc, by simpa [Valid, EventValid] using ev⟩
        exact ⟨s ++ [.consumed n skb stamp r, .buffered e], by simp only [hs, List.append_assoc]; rfl,
          hb, hb, by simpa using ev⟩

theorem valid_enter (e : Entry) (he : ConsumePayloadValid e) :
    PrefixPreserves (fun h _ => Valid h) Valid (enter e) := by
  unfold enter receiptObserved
  apply PrefixPreserves.bind (valid_emit (.entered e) he)
  intro _
  apply PrefixPreserves.bind (valid_access _).captureObserved
  intro r
  apply PrefixPreserves.bind (valid_emit (.completed e r) he)
  intro _
  exact PrefixPreserves.pure (I := fun h _ => Valid h) (S := Valid) (fun _ _ hi => hi) r.value

theorem valid_flush (es : List Entry) (he : ∀ e ∈ es, ConsumePayloadValid e) :
    PrefixPreserves (fun h _ => Valid h) Valid (flush es) := by
  induction es with
  | nil => simpa only [flush, List.forM_eq_forM, List.forM_nil] using
      (PrefixPreserves.pure (I := fun h _ => Valid h) (S := Valid) (fun _ _ hi => hi) ())
  | cons e es ih =>
    simp only [flush, List.forM_eq_forM, List.forM_cons]
    exact (valid_enter e (he e (by simp))).bind
      (fun _ => ih (fun x hx => he x (List.mem_cons_of_mem _ hx)))

def GroValid (g : Gro) : Prop := ∀ e ∈ g.rxList ++ g.held, ConsumePayloadValid e

abbrev Context (g : Gro) (h : List RxJoint.Event) (_ : World) : Prop := Valid h ∧ GroValid g

theorem keep (g : Gro) (a : Obs α)
    (ha : PrefixPreserves (fun h _ => Valid h) Valid a) :
    PrefixPreserves (Context g) Valid a := by
  intro w h hi
  obtain ⟨s, hs, hv, hn⟩ := ha w h hi.1
  refine ⟨s, hs, hv, ?_⟩
  cases hr : (runPrefix a w h).1 with
  | error e => trivial
  | ok out => exact ⟨by simpa only [hr] using hn, hi.2⟩

theorem normalList_valid (g : Gro) :
    PrefixEnsures (Context g) Valid (normalList g) Context := by
  unfold normalList
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi)
  · intro w h hi
    have hf := valid_flush g.rxList (fun e he => hi.2 e (List.mem_append_left _ he))
    change PrefixEnsures (fun h _ => Valid h) Valid _ (fun _ h _ => Valid h) at hf
    apply (PrefixEnsures.bind hf (fun _ => PrefixEnsures.pure (fun _ _ hv => hv)
      (fun _ _ hv => ⟨hv, fun e he => hi.2 e (List.mem_append_right _ (by simpa using he))⟩))) w h hi.1

theorem normalOne_valid (g : Gro) (e : Entry) (n : Nat) (he : ConsumePayloadValid e) :
    PrefixEnsures (Context g) Valid (normalOne g e n) Context := by
  have transfer : ∀ h w, Context g h w → Context {g with rxList := g.rxList ++ [e], rxCount := g.rxCount + n} h w := by
    intro h w hi
    refine ⟨hi.1, ?_⟩
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with (hx | rfl) | hx
    · exact hi.2 x (List.mem_append_left _ hx)
    · exact he
    · exact hi.2 x (List.mem_append_right _ hx)
  unfold normalOne
  dsimp only
  split
  · exact (normalList_valid _).consequence transfer (fun _ _ _ hi => hi)
  · exact PrefixEnsures.pure (fun _ _ hi => hi.1) transfer

theorem receive_valid (g : Gro) (e : Entry) (he : ConsumePayloadValid e) :
    PrefixEnsures (Context g) Valid (receive g e) Context := by
  unfold receive
  split
  · exact normalOne_valid _ _ _ he
  · have transfer : ∀ h w, Context g h w → Context {g with held := g.held ++ [e]} h w := by
      intro h w hi
      refine ⟨hi.1, ?_⟩
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx | rfl
      · exact hi.2 x (List.mem_append_left _ hx)
      · exact hi.2 x (List.mem_append_right _ hx)
      · exact he
    split
    · exact PrefixEnsures.bind (keep g _ (valid_lift _))
        (fun _ => PrefixEnsures.pure (fun _ _ hi => hi.1) transfer)
    · exact PrefixEnsures.pure (fun _ _ hi => hi.1) transfer

theorem valid_forIn (xs : List Entry) (g : Gro)
    (f : Entry → Gro → Obs (ForInStep Gro))
    (hf : ∀ e ∈ xs, ∀ g, PrefixEnsures (Context g) Valid (f e g)
      (fun step => Context step.value)) :
    PrefixEnsures (Context g) Valid (forIn xs g f) Context := by
  induction xs generalizing g with
  | nil => exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi)
  | cons e xs ih =>
    rw [List.forIn_cons]
    apply PrefixEnsures.bind (hf e (by simp) g)
    intro step
    cases step with
    | done g => exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi)
    | yield g => exact ih g (fun x hx g => hf x (List.mem_cons_of_mem _ hx) g)

theorem flushAll_valid (g : Gro) :
    PrefixEnsures (Context g) Valid (flushAll g) (fun _ h _ => Valid h) := by
  intro w h hi
  have held : ∀ e ∈ g.held, ConsumePayloadValid e := fun e he => hi.2 e (List.mem_append_right _ he)
  have pass : PrefixEnsures (Context g) Valid
      (forIn g.held g (fun e cur => do let out ← normalOne cur e 1; pure (.yield out))) Context := by
    apply valid_forIn
    intro e he cur
    exact PrefixEnsures.bind (normalOne_valid cur e 1 (held e he))
      (fun out => PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi))
  have whole : PrefixEnsures (Context g) Valid
      (do let cur ← forIn g.held g (fun e cur => do let out ← normalOne cur e 1; pure (.yield out))
          let _ ← normalList {cur with held := []}; pure ()) (fun _ h _ => Valid h) := by
    apply PrefixEnsures.bind pass
    intro cur
    apply PrefixEnsures.bind (Q := Context)
    · apply (normalList_valid {cur with held := []}).consequence
      · intro h w hi
        exact ⟨hi.1, fun e he => hi.2 e (List.mem_append_left _ (by simpa using he))⟩
      · intro _ _ _ hi; exact hi
    · intro _
      exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi.1)
  exact whole w h hi

theorem consume_context (g : Gro) (pid n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    PrefixEnsures (Context g) Valid (consume pid n skb stamp pkt ep)
      (fun out h w => Context g h w ∧ ∀ e ∈ out.toList, ConsumePayloadValid e) := by
  intro w h hi
  obtain ⟨s, hs, hv, hn⟩ := valid_consume pid n skb stamp pkt ep w h hi.1
  refine ⟨s, hs, hv, ?_⟩
  cases hr : (runPrefix (consume pid n skb stamp pkt ep) w h).1 with
  | error e => trivial
  | ok out =>
    simp only [hr] at hn
    exact ⟨⟨hn.1, hi.2⟩, hn.2⟩

theorem option_context (g : Gro) (out : Option Entry) :
    PrefixEnsures (fun h w => Context g h w ∧ ∀ e ∈ out.toList, ConsumePayloadValid e) Valid
      (forIn out.toList g (fun e cur => do let cur' ← receive cur e; pure (.yield cur'))) Context := by
  cases out with
  | none => exact PrefixEnsures.pure (fun _ _ hi => hi.1.1) (fun _ _ hi => hi.1)
  | some e =>
    intro w h hi
    have he := hi.2 e (by simp)
    simpa only [Option.toList_some, List.forIn_cons, List.forIn_nil, bind_assoc,
      pure_bind, bind_pure] using receive_valid g e he w h hi.1

theorem keep_bind (g : Gro) (a : Obs α) (f : α → Obs β)
    (ha : PrefixPreserves (fun h _ => Valid h) Valid a)
    (hf : ∀ x, PrefixEnsures (Context g) Valid (f x) Q) :
    PrefixEnsures (Context g) Valid (a >>= f) Q :=
  PrefixEnsures.bind (Q := fun _ => Context g) (keep g a ha) hf

theorem invariant_bind (g : Gro) (why : String) (f : Unit → Obs α) :
    PrefixEnsures (Context g) Valid (liftPrefix (invariant why) >>= f) Q := by
  intro w h hi
  exact ⟨[], by change h = h ++ []; simp, hi.1, True.intro⟩

theorem unsupported_bind (g : Gro) (why : String) (f : Unit → Obs α) :
    PrefixEnsures (Context g) Valid (liftPrefix (unsupported why) >>= f) Q := by
  intro w h hi
  exact ⟨[], by change h = h ++ []; simp, hi.1, True.intro⟩

macro "rx_receipt_step" : tactic => `(tactic|
  repeat' first
    | exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi)
    | exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi.1)
    | with_reducible apply invariant_bind
    | with_reducible apply unsupported_bind
    | with_reducible apply PrefixEnsures.bind (consume_context _ _ _ _ _ _ _)
    | with_reducible apply PrefixEnsures.bind (option_context _ _)
    | with_reducible apply PrefixEnsures.bind (flushAll_valid _)
    | with_reducible apply keep_bind _ _ _ (valid_state _ _ _ _)
    | with_reducible apply keep_bind _ _ _ (valid_counter _ _ _ _)
    | with_reducible apply keep_bind _ _ _ (valid_endpoint _ _ _ _)
    | with_reducible apply keep_bind _ _ _ (valid_drop _ _ _ _)
    | with_reducible apply keep_bind _ _ _ (valid_capture _)
    | with_reducible apply keep_bind _ _ _ (valid_access _)
    | with_reducible apply keep_bind _ _ _ (valid_lift _)
    | with_reducible apply PrefixEnsures.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split))

/-- Literal post-loop continuation, factored only as a proof cut. -/
theorem poll_tail_valid (pid : PeerId) (budget : Nat) (acc : Nat × Gro × Bool) :
    PrefixEnsures (Context acc.2.1) Valid
      (do
        if !acc.2.2 && acc.1 < budget then liftPrefix (invariant "the rx_queue did not drain")
        if ← liftPrefix (branch .rxPollComplete (acc.1 < budget)) then
          access (completeAccess pid)
          flushAll acc.2.1
        else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
        return acc.1)
      (fun _ h _ => Valid h) := by
  rx_receipt_step
  exact PrefixEnsures.pure (P := fun h _ => Valid h) (fun _ _ hi => hi) (fun _ _ hi => hi)

/-- Every actual consume receipt and every carried consume payload is valid,
including observations retained when this poll later Stops. -/
theorem poll_valid (pid : PeerId) (budget : Nat) :
    PrefixEnsures (Context {}) Valid (poll pid budget) (fun _ h _ => Valid h) := by
  unfold poll
  apply keep_bind {} _ _ (valid_lift _)
  intro noBudget
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi.1)
  · apply PrefixEnsures.bind (Q := fun acc : Nat × Gro × Bool => Context acc.2.1)
    · with_reducible apply (PrefixEnsures.rangeInvariant _ (0, ({} : Gro), false) _
        (fun acc : Nat × Gro × Bool => Context acc.2.1) Valid (fun _ _ _ hi => hi.1))
      intro index acc
      rx_receipt_step
    · intro acc
      exact poll_tail_valid pid budget acc

/-- Prior access history is arbitrary. Fresh metadata validity is independent
of allocation safety and does not assert validity of arbitrary old payloads. -/
theorem poll_seed_valid (pid : PeerId) (budget : Nat) (w : World) (prior : List LifetimeEvent) :
    Valid (runPrefix (poll pid budget) w (seed prior)).2 := by
  apply (poll_valid pid budget w (seed prior) ?_).choose_spec.2.1
  refine ⟨?_, by simp [GroValid]⟩
  intro e he
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp he
  trivial

/-- Selection settlement is chronological; callback completion is deliberately
not used here because GRO may reorder normal and held offers. -/
def settledKey : RxJoint.Event → Option EntryKey
  | .checkedState n skb stamp _ r => if r.value then some (n, skb, stamp) else none
  | .checkedCounter n skb stamp _ r => if r.value then none else some (n, skb, stamp)
  | .checkedEndpoint n skb stamp _ r => if r.value.isNone then some (n, skb, stamp) else none
  | .consumed n skb stamp r => if r.run.value.isNone then some (n, skb, stamp) else none
  | .buffered e => some e.key
  | _ => none

def settledKeys (h : List RxJoint.Event) := h.filterMap settledKey

def Account (pending : Option EntryKey) (h : List RxJoint.Event) : Prop :=
  removalKeys h = settledKeys h ++ pending.toList

def AccountSafe (h : List RxJoint.Event) : Prop := ∃ pending, Account pending h

theorem Account.safe (hi : Account p h) : AccountSafe h := ⟨p, hi⟩

theorem account_quiet (p : Option EntryKey) (a : Obs α) (ha : Appends a)
    (hm : HistoryFrame removedKey a) (hs : HistoryFrame settledKey a) :
    PrefixPreserves (fun h _ => Account p h) AccountSafe a := by
  intro w h hi
  obtain ⟨s, he⟩ := ha w h
  have hi' : Account p (runPrefix a w h).2 := by
    simpa only [Account, removalKeys, settledKeys, hm w h, hs w h] using hi
  refine ⟨s, he, hi'.safe, ?_⟩
  cases (runPrefix a w h).1 <;> trivial

theorem account_access (p : Option EntryKey) (a : MixedM α) :
    PrefixPreserves (fun h _ => Account p h) AccountSafe (access a) :=
  account_quiet p _ (access_appends a)
    (fun w h => focusPrefix_other RxJoint.Event.access accessEvent removedKey (fun _ => rfl) a w h)
    (fun w h => focusPrefix_other RxJoint.Event.access accessEvent settledKey (fun _ => rfl) a w h)

theorem account_lift (p : Option EntryKey) (a : M α) :
    PrefixPreserves (fun h _ => Account p h) AccountSafe (liftPrefix a) :=
  account_quiet p _ (Appends.lift a) (HistoryFrame.lift _ a) (HistoryFrame.lift _ a)

theorem account_capture (p : Option EntryKey) (skb : SkbId) :
    PrefixPreserves (fun h _ => Account p h) AccountSafe (capture skb) := by
  apply account_quiet p _ (capture_appends skb)
  all_goals intro w h; rw [capture_run]; cases (getRxSkb skb).run w <;>
    simp [List.filterMap_append, removedKey, settledKey]

theorem account_settle (k : EntryKey) (e : RxJoint.Event)
    (hm : removedKey e = none) (hs : settledKey e = some k) (hi : Account (some k) h) :
    Account none (h ++ [e]) := by
  simpa only [Account, removalKeys, settledKeys, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, hm, hs, List.append_nil, Option.toList_none, Option.toList_some] using hi

theorem account_ignore (p : Option EntryKey) (e : RxJoint.Event)
    (hm : removedKey e = none) (hs : settledKey e = none) (hi : Account p h) :
    Account p (h ++ [e]) := by
  simpa only [Account, removalKeys, settledKeys, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, hm, hs, List.append_nil] using hi

theorem account_drop (pid n skb : Nat) (stamp : PacketStamp) :
    PrefixEnsures (fun h _ => Account none h) AccountSafe (drop pid n skb stamp)
      (fun _ h _ => Account (some (n, skb, stamp)) h) := by
  unfold drop
  apply PrefixEnsures.bind (Q := fun _ h _ => Account none h) (account_access none _)
  intro _ w h hi
  have hn : Account (some (n, skb, stamp)) (h ++ [.removed n skb stamp]) := by
    simpa only [Account, removalKeys, settledKeys, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, removedKey, settledKey, List.append_nil, Option.toList_none, Option.toList_some] using
      congrArg (· ++ [(n, skb, stamp)]) hi
  exact ⟨[.removed n skb stamp], rfl, hn.safe, hn⟩

theorem account_receipt (k : EntryKey) (a : Obs α) (f : RunWitness α → RxJoint.Event)
    (done : α → Bool) (ha : PrefixPreserves (fun h _ => Account (some k) h) AccountSafe a)
    (hm : ∀ r, removedKey (f r) = none)
    (hs : ∀ r, settledKey (f r) = if done r.value then some k else none) :
    PrefixEnsures (fun h _ => Account (some k) h) AccountSafe (receiptObserved a f)
      (fun x h _ => Account (if done x then none else some k) h) := by
  intro w h hi
  obtain ⟨s, he, hv, hn⟩ := ha w h hi
  rw [runPrefix_receiptObserved]
  cases hr : runPrefix a w h with
  | mk result t =>
    simp only [hr] at he hv hn
    cases result with
    | error e => exact ⟨s, he, hv, True.intro⟩
    | ok out =>
      rcases out with ⟨x, v⟩
      have hout : Account (if done x then none else some k) (t ++ [f ⟨x, w, v⟩]) := by
        cases hd : done x
        · exact account_ignore _ _ (hm _) (by simpa [hd] using hs ⟨x, w, v⟩) hn
        · exact account_settle _ _ (hm _) (by simpa [hd] using hs ⟨x, w, v⟩) hn
      exact ⟨s ++ [f ⟨x, w, v⟩], by simp only [he, List.append_assoc], hout.safe, hout⟩

theorem account_consume (pid n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    PrefixEnsures (fun h _ => Account (some (n, skb, stamp)) h) AccountSafe
      (consume pid n skb stamp pkt ep) (fun _ h _ => Account none h) := by
  intro w h hi
  obtain ⟨s, hs, hv, hn⟩ := account_access (some (n, skb, stamp)) (consumeDataDonePrefix pid pkt ep) w h hi
  rw [consume_run]
  cases hr : runPrefix (access (consumeDataDonePrefix pid pkt ep)) w h with
  | mk result t =>
    simp only [hr] at hs hv hn
    cases result with
    | error e => exact ⟨s, hs, hv, True.intro⟩
    | ok out =>
      rcases out with ⟨out, v⟩
      let r : ConsumeReceipt := ⟨pid, pkt, ep, ⟨out, w, v⟩⟩
      cases out with
      | none =>
        have hc := account_settle (n, skb, stamp) (.consumed n skb stamp r) rfl rfl hn
        exact ⟨s ++ [.consumed n skb stamp r], by simp only [hs, List.append_assoc]; rfl, hc.safe, hc⟩
      | some bytes =>
        let e : Entry := ⟨⟨n, skb, bytes⟩, stamp, some r⟩
        have hc := account_ignore (some (n, skb, stamp)) (.consumed n skb stamp r) rfl rfl hn
        have hb := account_settle (n, skb, stamp) (.buffered e) rfl rfl hc
        exact ⟨s ++ [.consumed n skb stamp r, .buffered e], by simp only [hs, List.append_assoc]; rfl, hb.safe, hb⟩

theorem settled_access (a : MixedM α) : HistoryFrame settledKey (access a) :=
  fun w h => focusPrefix_other RxJoint.Event.access accessEvent settledKey (fun _ => rfl) a w h

theorem settled_enter (e : Entry) : HistoryFrame settledKey (enter e) := by
  unfold enter
  exact (HistoryFrame.emit _ rfl).bind (fun _ => (settled_access _).receiptObserved (fun _ => rfl))

theorem settled_flush (es : List Entry) : HistoryFrame settledKey (flush es) := by
  induction es with
  | nil => exact HistoryFrame.pure _ _
  | cons e es ih =>
    simp only [flush, List.forM_eq_forM, List.forM_cons] at *
    exact (settled_enter e).bind (fun _ => ih)

theorem settled_normalList (g : Gro) : HistoryFrame settledKey (normalList g) := by
  unfold normalList
  split
  · exact HistoryFrame.pure _ _
  · exact (settled_flush _).bind (fun _ => HistoryFrame.pure _ _)

theorem settled_normalOne (g : Gro) (e : Entry) (n : Nat) : HistoryFrame settledKey (normalOne g e n) := by
  unfold normalOne
  dsimp only
  split
  · exact settled_normalList _
  · exact HistoryFrame.pure _ _

theorem settled_receive (g : Gro) (e : Entry) : HistoryFrame settledKey (receive g e) := by
  unfold receive
  split
  · exact settled_normalOne _ _ _
  · split
    · exact (HistoryFrame.lift _ _).bind (fun _ => HistoryFrame.pure _ _)
    · exact HistoryFrame.pure _ _

theorem settled_flushAll (g : Gro) : HistoryFrame settledKey (flushAll g) := by
  unfold flushAll
  apply HistoryFrame.bind
  · apply HistoryFrame.forIn
    intro e g
    exact (settled_normalOne _ _ _).bind (fun _ => HistoryFrame.pure _ _)
  · intro g
    exact (settled_normalList _).bind (fun _ => HistoryFrame.pure _ _)

theorem account_receive (p : Option EntryKey) (g : Gro) (e : Entry) :
    PrefixPreserves (fun h _ => Account p h) AccountSafe (receive g e) :=
  account_quiet p _ (receive_appends _ _) (removalKeys_frame (receive_appends _ _) (receive_removed _ _)) (settled_receive _ _)

theorem account_flushAll (p : Option EntryKey) (g : Gro) :
    PrefixPreserves (fun h _ => Account p h) AccountSafe (flushAll g) :=
  account_quiet p _ (flushAll_appends _) (removalKeys_frame (flushAll_appends _) (flushAll_removed _)) (settled_flushAll _)

theorem account_state_bind (n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (f : Bool → Obs α)
    (hf : PrefixEnsures (fun h _ => Account (some (n, skb, stamp)) h) AccountSafe (f false) Q)
    (ht : PrefixEnsures (fun h _ => Account none h) AccountSafe (f true) Q) :
    PrefixEnsures (fun h _ => Account (some (n, skb, stamp)) h) AccountSafe
      (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (RxJoint.Event.checkedState n skb stamp pkt) >>= f) Q := by
  apply PrefixEnsures.bind (account_receipt (n, skb, stamp) _ _ id (account_lift _ _) (fun _ => rfl) (fun _ => rfl))
  intro b
  cases b
  · exact hf
  · exact ht

theorem account_counter_bind (n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (f : Bool → Obs α)
    (hf : PrefixEnsures (fun h _ => Account none h) AccountSafe (f false) Q)
    (ht : PrefixEnsures (fun h _ => Account (some (n, skb, stamp)) h) AccountSafe (f true) Q) :
    PrefixEnsures (fun h _ => Account (some (n, skb, stamp)) h) AccountSafe
      (receiptObserved (access (counterValidatePrefix pkt.keypair pkt.nonce))
        (RxJoint.Event.checkedCounter n skb stamp pkt) >>= f) Q := by
  have hs : ∀ r, settledKey (RxJoint.Event.checkedCounter n skb stamp pkt r) =
      if !r.value then some (n, skb, stamp) else none := by
    intro r; cases hr : r.value <;> simp [settledKey, hr]
  apply PrefixEnsures.bind (account_receipt (n, skb, stamp) _ _ Bool.not (account_access _ _) (fun _ => rfl) hs)
  intro b
  cases b
  · exact hf
  · exact ht

theorem account_endpoint_bind (n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (f : Option Endpoint → Obs α)
    (hn : PrefixEnsures (fun h _ => Account none h) AccountSafe (f none) Q)
    (hs : ∀ ep, PrefixEnsures (fun h _ => Account (some (n, skb, stamp)) h) AccountSafe (f (some ep)) Q) :
    PrefixEnsures (fun h _ => Account (some (n, skb, stamp)) h) AccountSafe
      (receiptObserved (liftPrefix (endpointFromSkb pkt.source))
        (RxJoint.Event.checkedEndpoint n skb stamp pkt) >>= f) Q := by
  apply PrefixEnsures.bind (account_receipt (n, skb, stamp) _ _ Option.isNone (account_lift _ _) (fun _ => rfl) (fun _ => rfl))
  intro ep
  cases ep
  · exact hn
  · exact hs _

theorem account_bind (p : Option EntryKey) (a : Obs α) (f : α → Obs β)
    (ha : PrefixPreserves (fun h _ => Account p h) AccountSafe a)
    (hf : ∀ x, PrefixEnsures (fun h _ => Account p h) AccountSafe (f x) Q) :
    PrefixEnsures (fun h _ => Account p h) AccountSafe (a >>= f) Q :=
  PrefixEnsures.bind (Q := fun _ h _ => Account p h) ha hf

theorem account_branch_bind (p : Option EntryKey) (d : Decision) (b : Bool) (f : Bool → Obs α)
    (hf : PrefixEnsures (fun h _ => Account p h) AccountSafe (f b) Q) :
    PrefixEnsures (fun h _ => Account p h) AccountSafe (liftPrefix (branch d b) >>= f) Q := by
  intro w h hi
  simpa only [runPrefix_bind, runPrefix_lift, CounterWindow.branch_run] using
    hf (CounterWindow.record w d b) h hi

theorem account_option (p : Option EntryKey) (out : Option Entry) (g : Gro) :
    PrefixPreserves (fun h _ => Account p h) AccountSafe
      (forIn out.toList g (fun e g => do let g' ← receive g e; pure (.yield g'))) :=
  PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    (fun e g => (account_receive p g e).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.safe) _))

theorem account_invariant (p : Option EntryKey) (why : String) (f : Unit → Obs α) :
    PrefixEnsures (fun h _ => Account p h) AccountSafe (liftPrefix (invariant why) >>= f) Q := by
  intro w h hi
  exact ⟨[], by change h = h ++ []; simp, hi.safe, True.intro⟩

theorem account_unsupported (p : Option EntryKey) (why : String) (f : Unit → Obs α) :
    PrefixEnsures (fun h _ => Account p h) AccountSafe (liftPrefix (unsupported why) >>= f) Q := by
  intro w h hi
  exact ⟨[], by change h = h ++ []; simp, hi.safe, True.intro⟩

macro "rx_account_step" : tactic => `(tactic|
  repeat' first
    | exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi)
    | with_reducible apply account_invariant
    | with_reducible apply account_unsupported
    | with_reducible apply account_state_bind
    | with_reducible apply account_counter_bind
    | with_reducible apply account_endpoint_bind
    | with_reducible apply account_branch_bind
    | with_reducible apply PrefixEnsures.bind (account_drop _ _ _ _)
    | with_reducible apply PrefixEnsures.bind (account_consume _ _ _ _ _ _)
    | with_reducible apply account_bind _ _ _ (account_option _ _ _)
    | with_reducible apply account_bind _ _ _ (account_flushAll _ _)
    | with_reducible apply account_bind _ _ _ (account_capture _ _)
    | with_reducible apply account_bind _ _ _ (account_access _ _)
    | with_reducible apply account_bind _ _ _ (account_lift _ _)
    | with_reducible apply PrefixEnsures.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split))

/-- Exact selection-phase accounting: failure leaves at most the current
removed occurrence unresolved; normal return settles every removal. -/
theorem poll_account (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun h _ => Account none h) AccountSafe (poll pid budget) := by
  change PrefixEnsures (fun h _ => Account none h) AccountSafe _ (fun _ h _ => Account none h)
  unfold poll
  apply account_branch_bind
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi)
  · apply PrefixEnsures.bind (Q := fun _ h _ => Account none h)
    · change PrefixPreserves (fun h _ => Account none h) AccountSafe _
      with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
      intro index acc
      change PrefixEnsures (fun h _ => Account none h) AccountSafe _ (fun _ h _ => Account none h)
      rx_account_step
      all_goals simp_all
    · intro acc
      rx_account_step
      all_goals simp_all

def nondeliveryKey : RxJoint.Event → Option EntryKey
  | .buffered _ => none
  | e => settledKey e

def bufferedKey : RxJoint.Event → Option EntryKey
  | .buffered e => some e.key
  | _ => none

theorem settled_partition (h : List RxJoint.Event) :
    (settledKeys h).Perm (h.filterMap nondeliveryKey ++ h.filterMap bufferedKey) := by
  induction h with
  | nil => exact .nil
  | cons e h ih =>
    cases e <;> simp only [settledKeys, List.filterMap_cons, settledKey, nondeliveryKey, bufferedKey] at *
    all_goals first
      | exact ih
      | exact (ih.cons _).trans List.perm_middle.symm
      | (split <;> simp_all only [Option.toList_none, List.cons_append] <;> first | exact ih | exact ih.cons _)

theorem buffered_keys_tags (h : List RxJoint.Event) :
    (h.filterMap bufferedKey).map Prod.fst =
      (bufferedEntries (h.filterMap groEvent)).map GroEntry.occurrence := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp only [bufferedKey, groEvent, bufferedEntries, Entry.key,
      List.filterMap_cons, List.map_cons] at * <;> first | exact ih | exact congrArg (_ :: ·) ih

theorem removed_keys_tags (h : List RxJoint.Event) :
    (removalKeys h).map Prod.fst = (removedTags (h.filterMap groEvent)).map Prod.fst := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp only [removalKeys, removedKey, groEvent, removedTags,
      List.filterMap_cons, List.map_cons] at * <;> first | exact ih | exact congrArg (_ :: ·) ih

def completedEntries (h : List RxJoint.Event) : List Entry :=
  (h.filterMap RxCompletion.jointEvent).filterMap RxCompletion.completed

def callbackPending (h : List RxJoint.Event) : List Entry :=
  (entries h).drop (completedEntries h).length

def unentered (h : List RxJoint.Event) : List GroEntry :=
  (selectedEntries (bufferedEntries (h.filterMap groEvent))).drop (entries h).length

theorem completion_remainder (h : List RxJoint.Event)
    (hp : RxCompletion.PrefixTrace (h.filterMap RxCompletion.jointEvent)) :
    entries h = completedEntries h ++ callbackPending h ∧ (callbackPending h).length ≤ 1 := by
  have split : ∃ p : Option Entry, entries h = completedEntries h ++ p.toList := by
    rcases hp with hc | ⟨pre, e, hc, he⟩
    · exact ⟨none, by simpa only [Option.toList_none, List.append_nil, completedEntries,
        RxCompletion.joint_entries] using hc.matches⟩
    · refine ⟨some e, ?_⟩
      rw [← RxCompletion.joint_entries, he]
      simp only [completedEntries, he, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, RxCompletion.entered, RxCompletion.completed, List.append_nil,
        hc.matches, Option.toList_some]
  obtain ⟨p, he⟩ := split
  have hd : callbackPending h = p.toList := by simp [callbackPending, he]
  exact ⟨by simpa only [hd] using he, by rw [hd]; cases p <;> simp⟩

theorem selected_remainder (h : List RxJoint.Event)
    (hs : SelectedGroSafe (h.filterMap groEvent)) :
    selectedEntries (bufferedEntries (h.filterMap groEvent)) =
      (entries h).map Entry.tag ++ unentered h := by
  obtain ⟨rest, he⟩ := hs
  change selectedEntries _ = enteredEntries _ ++ rest at he
  rw [← entries_tags] at he
  have hd : unentered h = rest := by simp [unentered, he]
  simpa only [hd] using he

/-- Occurrence partition from source-phase cuts. Disjointness additionally
uses the fresh poll's derived occurrence Nodup. The unentered list is the whole selected
GRO suffix (including an offered second held entry); it is not a claim that
all of that suffix is physically stored in GRO or in the RX packet store. -/
theorem partition_of_cuts (h : List RxJoint.Event) (pending : Option EntryKey)
    (ha : Account pending h) (hg : SelectedGroSafe (h.filterMap groEvent))
    (hc : RxCompletion.PrefixTrace (h.filterMap RxCompletion.jointEvent)) :
    ((removalKeys h).map Prod.fst).Perm
      ((h.filterMap nondeliveryKey).map Prod.fst ++
       (completedEntries h).map (fun e => e.tag.occurrence) ++
       (callbackPending h).map (fun e => e.tag.occurrence) ++
       (unentered h).map GroEntry.occurrence ++ pending.toList.map Prod.fst) ∧
      (callbackPending h).length ≤ 1 := by
  have hp := (settled_partition h).map Prod.fst
  simp only [List.map_append, buffered_keys_tags] at hp
  have hg' := (selectedEntries_perm (bufferedEntries (h.filterMap groEvent))).symm.map GroEntry.occurrence
  rw [selected_remainder h hg] at hg'
  simp only [List.map_append, List.map_map, Function.comp_def] at hg'
  obtain ⟨he, hl⟩ := completion_remainder h hc
  rw [he] at hg'
  simp only [List.map_append] at hg'
  have combined := hp.trans (hg'.append_left ((h.filterMap nondeliveryKey).map Prod.fst))
  have final := combined.append_right (pending.toList.map Prod.fst)
  refine ⟨?_, hl⟩
  change removalKeys h = settledKeys h ++ pending.toList at ha
  rw [ha]
  simpa only [List.map_append, List.append_assoc] using final

theorem poll_account_seed (pid : PeerId) (budget : Nat) (w : World) (prior : List LifetimeEvent) :
    AccountSafe (runPrefix (poll pid budget) w (seed prior)).2 ∧
      (match (runPrefix (poll pid budget) w (seed prior)).1 with
       | .error _ => True
       | .ok _ => Account none (runPrefix (poll pid budget) w (seed prior)).2) := by
  have initial : Account none (seed prior) := by
    simp only [Account, removalKeys, settledKeys, seed, Option.toList_none, List.append_nil]
    rw [filterMap_disjoint RxJoint.Event.access removedKey (fun _ => rfl),
      filterMap_disjoint RxJoint.Event.access settledKey (fun _ => rfl)]
  obtain ⟨_, _, hs, hn⟩ := poll_account pid budget w (seed prior) initial
  refine ⟨hs, ?_⟩
  cases hr : (runPrefix (poll pid budget) w (seed prior)).1 with
  | error e => trivial
  | ok out => rcases out with ⟨x, v⟩; simpa only [hr] using hn

/-- Every fresh poll prefix partitions actual removal occurrences. No initial
allocation invariant or successful return is assumed. Only one currently
selected occurrence and one entered callback can remain unfinished. -/
theorem poll_partition (pid : PeerId) (budget : Nat) (w : World) (prior : List LifetimeEvent) :
    let h := (runPrefix (poll pid budget) w (seed prior)).2
    ∃ pending : Option EntryKey,
      Account pending h ∧
      ((removalKeys h).map Prod.fst).Perm
        ((h.filterMap nondeliveryKey).map Prod.fst ++
         (completedEntries h).map (fun e => e.tag.occurrence) ++
         (callbackPending h).map (fun e => e.tag.occurrence) ++
         (unentered h).map GroEntry.occurrence ++ pending.toList.map Prod.fst) ∧
      (callbackPending h).length ≤ 1 ∧ ((removalKeys h).map Prod.fst).Nodup := by
  dsimp only
  let h := (runPrefix (poll pid budget) w (seed prior)).2
  obtain ⟨pending, ha⟩ := (poll_account_seed pid budget w prior).1
  have hg := rxPollGro_selected_prefix pid budget w
  have ht := rxPollGro_tags_safe pid budget w
  have he := congrArg Prod.snd (poll_fresh_gro pid budget w prior)
  rw [he] at hg ht
  obtain ⟨_, _, hc, _⟩ := RxCompletion.poll_preserves pid budget w (seed prior)
    (by simp only [RxCompletion.Closed, RxCompletion.seed_empty]; exact RxCompletion.ClosedTrace.nil)
  have hd : ((removalKeys h).map Prod.fst).Nodup := by
    rw [removed_keys_tags, ht.properties.2.1]
    exact List.nodup_range
  exact ⟨pending, ha, (partition_of_cuts h pending ha hg hc).1,
    (partition_of_cuts h pending ha hg hc).2, hd⟩

/-- Normal poll return leaves no selection, GRO-offer or callback residual.
The partition is by occurrence and therefore remains valid with aliased slots;
allocation identity is handled separately by the existing stamp theorem. -/
theorem poll_normal_partition (pid : PeerId) (budget : Nat) (w v : World)
    (prior : List LifetimeEvent) (n : Nat)
    (hr : (runPrefix (poll pid budget) w (seed prior)).1 = .ok (n, v)) :
    let h := (runPrefix (poll pid budget) w (seed prior)).2
    Account none h ∧ callbackPending h = [] ∧ unentered h = [] ∧
      ((removalKeys h).map Prod.fst).Perm
        ((h.filterMap nondeliveryKey).map Prod.fst ++
          (completedEntries h).map (fun e => e.tag.occurrence)) ∧
      (((h.filterMap nondeliveryKey).map Prod.fst ++
          (completedEntries h).map (fun e => e.tag.occurrence))).Nodup := by
  dsimp only
  let h := (runPrefix (poll pid budget) w (seed prior)).2
  have ha : Account none h := by simpa only [hr] using (poll_account_seed pid budget w prior).2
  have original := (poll_erases pid budget w (seed prior)).symm.trans hr
  have hg := rxPollGro_selected_complete pid budget w v n original
  have he := congrArg Prod.snd (poll_fresh_gro pid budget w prior)
  rw [he] at hg
  obtain ⟨_, _, hc, hn⟩ := RxCompletion.poll_preserves pid budget w (seed prior)
    (by simp only [RxCompletion.Closed, RxCompletion.seed_empty]; exact RxCompletion.ClosedTrace.nil)
  have closed : RxCompletion.ClosedTrace (h.filterMap RxCompletion.jointEvent) := by
    simpa only [hr, RxCompletion.Closed] using hn
  have entries_eq : entries h = completedEntries h := by
    simpa only [RxCompletion.joint_entries, completedEntries] using closed.matches
  have hpending : callbackPending h = [] := by simp [callbackPending, entries_eq]
  have hunentered : unentered h = [] := by
    change selectedEntries (bufferedEntries (h.filterMap groEvent)) = enteredEntries (h.filterMap groEvent) at hg
    rw [← entries_tags] at hg
    simp [unentered, hg]
  have part := (partition_of_cuts h none ha hg.safe hc).1
  have part' : ((removalKeys h).map Prod.fst).Perm
      ((h.filterMap nondeliveryKey).map Prod.fst ++
        (completedEntries h).map (fun e => e.tag.occurrence)) := by
    simpa only [hpending, hunentered, List.map_nil, Option.toList_none, List.append_nil] using part
  obtain ⟨_, _, _, _, hd⟩ := poll_partition pid budget w prior
  exact ⟨ha, hpending, hunentered, part', part'.nodup_iff.mp hd⟩

/-- Named decisions are decisions about nondelivery, not assertions that later
put/free cleanup completed. None receipts additionally have the original
keepalive/header/length or repaid peer-mismatch classification above. -/
theorem poll_receipts (pid : PeerId) (budget : Nat) (w : World) (prior : List LifetimeEvent) :
    let h := (runPrefix (poll pid budget) w (seed prior)).2
    (∀ occurrence skb stamp r, RxJoint.Event.consumed occurrence skb stamp r ∈ h → r.Valid) ∧
    (∀ e r, RxJoint.Event.completed e r ∈ h → ConsumePayloadValid e ∧ r.Valid (Stack.receive e.tag.bytes)) ∧
    (∀ e, RxJoint.Event.buffered e ∈ h → ConsumePayloadValid e) := by
  dsimp only
  have hv := poll_seed_valid pid budget w prior
  have hc := (RxCompletion.poll_preserves pid budget w (seed prior)
    (by simp only [RxCompletion.Closed, RxCompletion.seed_empty]; exact RxCompletion.ClosedTrace.nil)).choose_spec.2.1
  refine ⟨fun n skb stamp r hm => hv _ hm, ?_, fun e hm => hv _ hm⟩
  intro e r hm
  refine ⟨hv _ hm, ?_⟩
  have hm' : RxCompletion.Step.completed e r ∈
      ((runPrefix (poll pid budget) w (seed prior)).2.filterMap RxCompletion.jointEvent) :=
    List.mem_filterMap.mpr ⟨.completed e r, hm, rfl⟩
  rcases hc with hc | ⟨pre, last, hc, he⟩
  · exact hc.receipts e r hm'
  · rw [he] at hm'
    simp only [List.mem_append, List.mem_singleton] at hm'
    rcases hm' with old | impossible
    · exact hc.receipts e r old
    · cases impossible

/-- The endpoint helper has no normal None path: malformed families and the
unsupported IPv6 source stop instead. This is not a new reachable drop class. -/
theorem endpoint_none_impossible (pkt : RxPacket) (r : RunWitness (Option Endpoint))
    (hv : r.Valid (endpointFromSkb pkt.source)) (hn : r.value = none) : False := by
  have spec : ⦃fun _ => ⌜True⌝⦄ endpointFromSkb pkt.source
      ⦃⇓? out _ => ⌜out.isSome = true⌝⦄ := by
    mvcgen [endpointFromSkb, branch]
    all_goals simp_all
  have hsome := (hoare_iff_triple _ _ _).mpr spec r.before r.value r.after True.intro hv
  simpa only [hn, Option.isSome_none, Bool.false_eq_true] using hsome

/-- Promotion retains exactly the new suffix at the actual incoming audit seed.
Old interleaved probe markers are preserved; arbitrary old metadata is not
asserted valid, and poll-local occurrence ordinals are not global identities. -/
theorem observePoll_receipt_suffix (pid : PeerId) (budget : Nat) (w : World)
    (h : List RxHistory.Event) :
    ∃ suffix : List RxJoint.Event,
      (runPrefix (poll pid budget) w (seed (RxHistory.prior h))).2 =
        seed (RxHistory.prior h) ++ suffix ∧
      runPrefix (RxHistory.observePoll pid budget) w h =
        ((runPrefix (poll pid budget) w (seed (RxHistory.prior h))).1,
          h ++ suffix.map RxHistory.promote) ∧ Valid suffix := by
  obtain ⟨suffix, hs⟩ := poll_appends pid budget w (seed (RxHistory.prior h))
  have hv := poll_seed_valid pid budget w (RxHistory.prior h)
  rw [hs] at hv
  exact ⟨suffix, hs, RxHistory.observePoll_suffix pid budget w h _ suffix (Prod.ext rfl hs),
    (valid_append _ _).mp hv |>.2⟩

end Leanux.Proofs.WG.Queues.RxDisposition
