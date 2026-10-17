import Leanux.Proofs.WG.Queues.RxStableFrames

/-! Stable boundary facts for the unchanged stamped poll observer. Every
normal endpoint is obtained from the same run; failed runs keep their actual
appended journal without asserting a returned world. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
open RxJoint PollCarrier

private theorem native_run (a : WG.M α) (w v : World) (x : α)
    (hr : (liftWG a).run w = .ok (x,v)) :
    (a.run w.wg).run w.ambient = .ok ((x,v.wg),v.ambient) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) a w v x hr

/-- An arbitrary product observer retains its original domain. The additional
stable boundary is transported only by its explicit normal-run contract. -/
theorem stable_observed {α β : Type} {initial : Ledger}
    {P : List RxJoint.Event → World → Prop} {Q : α → List RxJoint.Event → World → Prop}
    (a : Obs α) (original : Leanux.M β) (p : α → β)
    (ha : Appends a) (he : ErasesTo p a original) (hf : HistoryFrame removedStamp a)
    (old : PrefixEnsures P (fun _ => True) a Q)
    (keep : ∀ w h x v, P h w → StableRx (rest initial h) w.wg →
      original.run w = .ok (x,v) → StableRx (rest initial h) v.wg) :
    PrefixEnsures (fun h w => P h w ∧ StableRx (rest initial h) w.wg) (fun _ => True) a
      (fun x h w => Q x h w ∧ StableRx (rest initial h) w.wg) := by
  apply normal_spec ha
  intro w h x v hi hr
  have post := (old w h hi.1).choose_spec.2.2
  rw [hr] at post
  have run : original.run w = .ok (p x,v) := by rw [←he w h,hr]; rfl
  refine ⟨post,?_⟩
  change StableRx (remaining initial (removedPackets (runPrefix a w h).2)) v.wg
  rw [removed_frame hf]
  exact keep w h _ v hi.1 hi.2 run

private theorem stack_stable (cs : Ledger) (packets : List (List UInt8)) :
    Preserves (fun w : World => KeysCompatible w.wg ∧ StableRx cs w.wg)
      (packets.forM Leanux.Env.deliverInner) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w u v hi hr
  cases u
  have old := (hoare_iff_run _ _ _).mp (stackForM_stack w.wg packets)
    w () v ⟨Transfer.refl w.wg,hi.1⟩ hr
  exact ⟨old.2,stable_stack packets hi.2 hi.1 hr⟩

private theorem gro_stable (cs : Ledger) (g : GroState) (bytes : List UInt8) :
    Preserves (fun w : World => KeysCompatible w.wg ∧ StableRx cs w.wg)
      (napiGroReceive (fun xs => xs.forM Leanux.Env.deliverInner) g bytes) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groReceive_preserves)
    _ _ (stack_stable cs) g bytes

private theorem flush_stable (cs : Ledger) (g : GroState) :
    Preserves (fun w : World => KeysCompatible w.wg ∧ StableRx cs w.wg)
      (napiGroFlushAll (fun xs => xs.forM Leanux.Env.deliverInner) g) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groFlush_preserves)
    _ _ (stack_stable cs) g

theorem stable_receive_observed (initial : Ledger) (loans : Reservations)
    (pid skb : Nat) (stamp : PacketStamp) (g : Gro) (e : Entry) :
    PrefixPreserves (fun h w => Bare initial loans pid skb stamp h w ∧
      StableRx (rest initial h) w.wg) (fun _ => True) (receive g e) := by
  apply stable_observed _ _ _ (receive_appends g e)
    (projected_erases (receive_gro g e) (napiGroReceiveTagged_erases g.forget e.tag))
    (receive_removed g e) (bare_receive initial loans pid skb stamp g e)
  intro w h x v hi hs hr
  obtain ⟨o,_,_,hc⟩ := hi
  exact ((hoare_iff_run _ _ _).mp (gro_stable (rest initial h) g.erase e.tag.bytes) w x v ⟨hc.keys,hs⟩ hr).2

theorem stable_flush_observed (initial : Ledger) (loans : Reservations) (g : Gro) :
    PrefixPreserves (fun h w => Ready initial loans h w ∧ StableRx (rest initial h) w.wg)
      (fun _ => True) (flushAll g) := by
  apply stable_observed _ _ _ (flushAll_appends g)
    (projected_erases (flushAll_gro g) (napiGroFlushAllTagged_erases g.forget).to_projected)
    (flushAll_removed g) (context_flush [] initial loans g)
  intro w h x v hi hs hr
  exact ((hoare_iff_run _ _ _).mp (flush_stable (rest initial h) g.erase) w x v ⟨hi.keys,hs⟩ hr).2

theorem stable_consume_observed (initial : Ledger) (loans : Reservations) (pid n skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) (guard : pkt.peer = pid) :
    PrefixEnsures (fun h w => Live initial loans pid skb stamp pkt h w ∧
      StableRx (rest initial h) w.wg) (fun _ => True) (consume pid n skb stamp pkt ep)
      (fun _ h w => Bare initial loans pid skb stamp h w ∧ StableRx (rest initial h) w.wg) := by
  apply normal_spec (consume_appends _ _ _ _ _ _)
  intro w h result v hi hr
  have old := (consume_observed initial loans pid n skb stamp pkt ep guard w h hi.1).choose_spec.2.2
  rw [hr] at old
  refine ⟨old,?_⟩
  have frame := removed_frame (consume_removed pid n skb stamp pkt ep) w h
  change StableRx (remaining initial (removedPackets (runPrefix _ w h).2)) v.wg
  rw [frame]
  rw [consume_run] at hr
  cases ha : runPrefix (access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk result t => cases result with
    | error e => simp [ha] at hr
    | ok out =>
      rcases out with ⟨out,a⟩
      have original := (access_erases (liftWGObserver_erases (consumeDataDonePrefix_erases pid pkt ep)) w h).symm.trans (congrArg Prod.fst ha)
      have stable := stable_consumeDataDone pid pkt ep hi.2 w.ambient a.ambient (native_run _ w a out original)
      cases out <;> simp only [ha,Except.ok.injEq,Prod.mk.injEq] at hr
      all_goals obtain ⟨_,av⟩ := hr; subst a; exact stable

theorem stable_cleanup_observed (initial : Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (flag : Bool) (guard : pkt.peer = pid) :
    PrefixEnsures (fun h w => Bare initial loans pid skb stamp h w ∧
      StableRx (rest initial h) w.wg) (fun _ => True)
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _ ← liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb)))
      (fun _ h w => Ready initial loans h w ∧ StableRx (rest initial h) w.wg) := by
  let a : Obs Unit := do
    access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
    access (liftWGObserver (peerPutMixed (some pid)))
    _ ← liftPrefix (branch .rxPollFree flag)
    access (liftWGObserver (freeRxSkbPrefix skb))
  have he : ErasesPrefix a (liftWG (cleanup skb pkt flag)) := by
    rw [cleanup_poll_guard skb pkt pid flag guard]
    simp only [liftWG_bind]
    exact erasesPrefix_bind (access_erases (liftWGObserver_erases (keypairPutPrefix_erases _ _))) (fun _ =>
      erasesPrefix_bind (access_erases (liftWGObserver_erases (peerPutMixed_erases _))) (fun _ =>
      erasesPrefix_bind (erasesPrefix_lift _) (fun _ => access_erases (liftWGObserver_erases (freeRxSkbPrefix_erases _)))))
  have ha : Appends a := (access_appends _).bind (fun _ =>
    (access_appends _).bind (fun _ => (Appends.lift _).bind (fun _ => access_appends _)))
  have hf : HistoryFrame removedStamp a := (access_removed _).bind (fun _ =>
    (access_removed _).bind (fun _ => (HistoryFrame.lift _ _).bind (fun _ => access_removed _)))
  apply stable_observed a _ id ha he.to_projected hf
    (cleanup_observed initial loans pid skb stamp pkt flag guard)
  intro w h result v hi hs hr
  cases result
  obtain ⟨o,ho,hstamp,hc⟩ := hi
  have slot : (Selected stamp o).packet.slot = skb := by simp [Selected,packetOfStamp,hstamp]
  exact stable_selected_cleanup hs hc rfl (guard.trans ho.symm) w.ambient v.ambient
    (slot ▸ native_run _ w v () hr)

/-- A finite loop distinguishes resumed iterations from early exits. The
postcondition may record a fact established only at the actual break. -/
theorem stable_forIn_exit (xs : List α) (b : β)
    (g : α → β → PrefixT Event State (ForInStep β))
    (I J : β → List Event → State → Prop) (S : List Event → Prop)
    (safeI : ∀ b h w, I b h w → S h) (safeJ : ∀ b h w, J b h w → S h)
    (finish : ∀ b h w, I b h w → J b h w)
    (step : ∀ x b, PrefixEnsures (I b) S (g x b)
      (fun out => match out with | .yield b => I b | .done b => J b)) :
    PrefixEnsures (I b) S (forIn xs b g) J := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using PrefixEnsures.pure (safeI b) (finish b)
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply PrefixEnsures.bind (step x b)
    intro out
    cases out with
    | done b => exact PrefixEnsures.pure (safeJ b) (fun _ _ h => h)
    | yield b => exact ih b

def StableAt (initial : Ledger) (h : List RxJoint.Event) (w : World) :=
  StableRx (rest initial h) w.wg

def HeadAt (pid : PeerId) (first : Option SkbId) (w : World) :=
  ∀ d p, w.wg.dev = some d → d.peers[pid]? = some p → first = p.rxQueue.all.head?

def ReadyPacket (first : Option SkbId) (w : World) :=
  ∀ (id : SkbId) (pkt : RxPacket), first = some id → (RxDisposition.nativeRxStore w.wg).2 id = some pkt →
    pkt.state ≠ .uncrypted

theorem stable_peek_observed (initial : Ledger) (loans : Reservations) (pid : PeerId) :
    PrefixEnsures (fun h w => Ready initial loans h w ∧ StableAt initial h w)
      (fun _ => True) (access (liftWGObserver (peekAccess pid)))
      (fun first h w => AfterPeek initial loans pid first h w ∧
        StableAt initial h w ∧ HeadAt pid first w) := by
  apply normal_spec (access_appends _)
  intro w h first v hi hr
  have old := (peek_observed initial loans pid w h hi.1).choose_spec.2.2
  rw [hr] at old
  have original := (access_erases (liftWGObserver_erases (peekAccess_erases pid)) w h).symm.trans hr
  have run := native_run _ w v first original
  refine ⟨old,?_,peek_head pid w.wg v.wg first w.ambient v.ambient run⟩
  change StableRx (remaining initial (removedPackets (runPrefix _ w h).2)) v.wg
  rw [removed_frame (access_removed _)]
  exact stable_peek pid hi.2 w.ambient v.ambient run

theorem stable_ready_observed (initial : Ledger) (loans : Reservations) (pid : PeerId)
    (first : Option SkbId) :
    PrefixEnsures (fun h w => AfterPeek initial loans pid first h w ∧
      StableAt initial h w ∧ HeadAt pid first w) (fun _ => True)
      (access (liftWGObserver (readyAccess first)))
      (fun go h w => AfterPeek initial loans pid first h w ∧ StableAt initial h w ∧
        (go = false → ColdHead pid w.wg) ∧ (go = true → ReadyPacket first w)) := by
  apply normal_spec (access_appends _)
  intro w h go v hi hr
  have old := (ready_observed initial loans pid first w h hi.1).choose_spec.2.2
  rw [hr] at old
  have original := (access_erases (liftWGObserver_erases (readyAccess_erases first)) w h).symm.trans hr
  have run := native_run _ w v go original
  have same := (ready_result first w.wg v.wg go w.ambient v.ambient run).1
  refine ⟨old,?_,?_,?_⟩
  · change StableRx (remaining initial (removedPackets (runPrefix _ w h).2)) v.wg
    rw [removed_frame (access_removed _),same]
    exact hi.2.1
  · intro eq
    subst go
    exact ready_false_cold pid first hi.2.2 w.ambient v.ambient run
  · intro eq id pkt firstEq stored
    subst go
    subst first
    rw [same] at stored
    cases hd : w.wg.dev with
    | none => simp [RxDisposition.nativeRxStore,hd] at stored
    | some d =>
      have cell : d.rxSkbs[id]? = some pkt := by simpa [RxDisposition.nativeRxStore,hd] using stored
      exact ready_true_packet hd cell w.ambient v.ambient run

theorem stable_capture_observed (initial : Ledger) (loans : Reservations) (pid skb : Nat) :
    PrefixEnsures (fun h w => AfterPeek initial loans pid (some skb) h w ∧
      StableAt initial h w ∧ ReadyPacket (some skb) w) (fun _ => True) (capture skb)
      (fun out h w => Captured initial loans pid skb out h w ∧ StableAt initial h w ∧
        out.1.state ≠ .uncrypted) := by
  apply normal_spec (capture_appends skb)
  intro w h out v hi hr
  have old := (capture_observed initial loans pid skb w h hi.1).choose_spec.2.2
  rw [hr] at old
  obtain ⟨same,selected⟩ := RxDisposition.capture_selected skb w v h out.1 out.2 hr
  subst v
  refine ⟨old,?_,hi.2.2 skb out.1 rfl selected.2⟩
  have frame : HistoryFrame removedStamp (capture skb) := by
    intro w h
    rw [capture_run]
    cases (liftWG (getRxSkb skb)).run w <;> simp [removedStamp,List.filterMap_append]
  change StableRx (remaining initial (removedPackets (runPrefix _ w h).2)) w.wg
  rw [removed_frame frame]
  exact hi.2.1

theorem stable_complete_observed (initial : Ledger) (loans : Reservations) (pid : PeerId) :
    PrefixEnsures (fun h w => Ready initial loans h w ∧ StableAt initial h w ∧ ColdHead pid w.wg)
      (fun _ => True) (access (liftWGObserver (completeAccess pid)))
      (fun _ h w => Ready initial loans h w ∧ StableAt initial h w) := by
  apply normal_spec (access_appends _)
  intro w h u v hi hr
  cases u
  have old := ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.PollCarrier.context_native_access)
    [] initial loans (completeAccess pid) (completeAccess_erases pid) (complete_carrierView pid) w h hi.1).choose_spec.2.2
  rw [hr] at old
  have original := (access_erases (liftWGObserver_erases (completeAccess_erases pid)) w h).symm.trans hr
  refine ⟨old,?_⟩
  change StableRx (remaining initial (removedPackets (runPrefix _ w h).2)) v.wg
  rw [removed_frame (access_removed _)]
  exact hi.2.1.complete hi.2.2 w.ambient v.ambient (native_run _ w v () original)

end Leanux.Proofs.WG.Queues.RxCredits
