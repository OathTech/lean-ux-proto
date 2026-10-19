import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeCookie

/-! Original Noise consumers retain exactly one source-acquired loan on
success and repay it on refusal, over the same durable account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders HandshakeLoans
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

def Acquired (holders : DurableHolders) (cs : Ledger) (loans : Reservations)
    (result : Option PeerId) (w : WGWorld) : Prop :=
  match result with
  | none => Account holders cs loans w
  | some pid => ∃ owner : Owner, owner.slot = pid ∧ Account holders cs (owner :: loans) w

private theorem stop (why : String) : Hoare (invariant why : WG.M α) P Q := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  cases run

private theorem step {P : WGWorld → Prop} {Q : α → WGWorld → Prop}
    (action : WG.M β) (ha : Preserves P action) (tail : β → WG.M α)
    (ht : ∀ x, Hoare (tail x) P Q) : Hoare (action >>= tail) P Q :=
  hoare_bind _ _ ha ht

private theorem update_step (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (fields : ∀ p, (f p).internalId=p.internalId ∧ (f p).refcount=p.refcount ∧
      (f p).rxQueue=p.rxQueue ∧ (f p).napiScheduled=p.napiScheduled ∧
      (f p).keypairCurrent=p.keypairCurrent ∧ (f p).txQueue.all=p.txQueue.all)
    (ht : ∀x, Hoare (tail x) (Account holders cs loans) Q) :
    Hoare (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) (Account holders cs loans) Q := by
  have same := Account.update (holders := holders) (cs := cs) (loans := loans) pid f
    (fun p => (fields p).1) (fun p => (fields p).2.1) (fun p => (fields p).2.2.1)
    (fun p => (fields p).2.2.2.1) (fun p _ h => (fields p).2.2.2.2.1 ▸ h)
    (fun p => (fields p).2.2.2.2.2)
  simpa only [bind_assoc] using step _ same tail ht

private theorem failed (o : Owner) : Hoare (do peerPut (some o.slot); pure none)
    (Account holders cs (o::loans)) (Acquired holders cs loans) := by
  apply hoare_bind _ _ (payment o)
  intro u
  apply hoare_consequence (hoare_pure none (Account holders cs loans))
  · exact fun _ h => h
  · intro result w h
    rcases h with ⟨rfl,h⟩
    exact h

private theorem succeeded (o : Owner) : Hoare (pure (some o.slot) : WG.M (Option PeerId))
    (Account holders cs (o::loans)) (Acquired holders cs loans) := by
  apply hoare_consequence (hoare_pure (some o.slot) (Account holders cs (o::loans)))
  · exact fun _ h => h
  · intro result w h
    rcases h with ⟨rfl,h⟩
    exact ⟨o,rfl,h⟩

theorem response_tail (msg : List UInt8) (identity : StaticIdentity) (o : Owner) :
    Hoare (responseTail msg identity o.slot) (Account holders cs (o::loans)) (Acquired holders cs loans) := by
  unfold responseTail
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (loan_update_head
       apply update_step
       · intro p; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
       intro x)
    | (loan_bind_head peerPut; exact failed o)
    | (index_material_head invariant; exact stop _)
    | (index_material_head Pure.pure; first | exact succeeded o | exact preserves_pure _)
    | (index_material_head Bind.bind; apply step)
    | (index_material_head getPeer; exact read _)
    | loan_crypto (Account holders cs (o::loans))
    | material_component
    | material_intro
    | material_reduce
    | (index_material_head ite; split)
    | material_match

/-- Normal None repays the actual lookup reference; Some retains it as one
named loan. No successful-acquisition or positive-credit input is assumed. -/
theorem response (msg : List UInt8) (hi : Account holders cs loans w) (a b : Ambient)
    (run : ((consumeResponse msg).run w).run a=.ok ((result,v),b)) :
    Acquired holders cs loans result v := by
  have branch_run (decision : Decision) (value : Bool) (g : WGWorld) (t : Ambient) :
      ((branch decision value : WG.M Bool).run g).run t =
        .ok ((value,g),CounterWindow.record t decision value) := rfl
  rw [consumeResponse_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨d,read,c,getter,tail⟩ := run
  obtain ⟨rfl,rfl,hd⟩ := DecryptCarrier.getDev_current a c getter
  simp only [StateT.run_bind,branch_run,CounterWindow.except_ok_bind] at tail
  split at tail
  · cases tail; exact hi
  · rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨entry,acquired,e,lookup,rest⟩ := tail
    cases entry with
    | none =>
      simp only [StateT.run_bind,branch_run,CounterWindow.except_ok_bind,Option.isNone_none,ite_true] at rest
      cases rest
      exact hi.lookup_none _ _ lookup
    | some entry =>
      obtain ⟨owner,pid⟩ := entry
      simp only [StateT.run_bind,branch_run,CounterWindow.except_ok_bind,Option.isNone_some,
        Bool.false_eq_true,ite_false] at rest
      cases owner with
      | keypair id => cases rest
      | handshake id =>
        obtain ⟨dev,p,_,_,_,acquiredInv⟩ := hi.lookup _ _ lookup
        exact (hoare_iff_run_ambient _ _ _).mp (response_tail msg d.staticIdentity ⟨dev.ifindex,pid,p.internalId⟩)
          acquired _ result v b acquiredInv rest

private theorem out_failed (o : Owner) : Hoare (initiationOut (some o.slot) none)
    (Account holders cs (o::loans)) (Acquired holders cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  change ((do peerPut (some o.slot); pure none : WG.M (Option PeerId)).run w).run
    (CounterWindow.record a .consumeFailedPut true) = .ok ((result,v),b) at run
  exact (hoare_iff_run_ambient _ _ _).mp (failed o) w _ result v b hi run

private theorem out_success (o : Owner) : Hoare (initiationOut (some o.slot) (some o.slot))
    (Account holders cs (o::loans)) (Acquired holders cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  change Except.ok ((some o.slot,w),CounterWindow.record a .consumeFailedPut false) =
    .ok ((result,v),b) at run
  cases run
  exact ⟨o,rfl,hi⟩

private theorem out_none : Hoare (initiationOut none none) (Account holders cs loans) (Acquired holders cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  change Except.ok ((none,w),CounterWindow.record (CounterWindow.record a .consumeFailedPut true) .peerPutNull true) =
    .ok ((result,v),b) at run
  cases run
  exact hi

theorem initiation_tail (msg e ck hash : List UInt8) (o : Owner) :
    Hoare (initiationTail msg e ck hash (some o.slot) o.slot) (Account holders cs (o::loans)) (Acquired holders cs loans) := by
  unfold initiationTail WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (loan_update_head
       apply update_step
       · intro p; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
       intro x)
    | (index_material_head initiationOut; first | exact out_failed o | exact out_success o)
    | (index_material_head invariant; exact stop _)
    | (index_material_head Pure.pure; first | exact succeeded o | exact preserves_pure _)
    | (index_material_head Bind.bind; apply step)
    | (index_material_head getPeer; exact read _)
    | (index_material_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp (Account holders cs (o::loans)))
    | loan_crypto (Account holders cs (o::loans))
    | material_component
    | material_intro
    | material_reduce
    | (index_material_head ite; split)
    | material_match

private theorem afterLookup_result (msg e ck hash : List UInt8) (peer : Option PeerId) :
    Hoare (initiationAfterLookup msg e ck hash peer) (Acquired holders cs loans peer) (Acquired holders cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases peer with
  | none =>
    change ((initiationOut none none).run w).run (CounterWindow.record a .consumeNoPeer true) =
      .ok ((result,v),b) at run
    exact (hoare_iff_run_ambient _ _ _).mp out_none w _ result v b hi run
  | some pid =>
    obtain ⟨o,slot,hi⟩ := hi
    change ((initiationTail msg e ck hash (some pid) pid).run w).run (CounterWindow.record a .consumeNoPeer false) =
      .ok ((result,v),b) at run
    exact (hoare_iff_run_ambient _ _ _).mp (initiation_tail msg e ck hash o)
      w _ result v b hi (by simpa only [slot] using run)

private theorem lookup_then (key : Key) (msg e ck hash : List UInt8) :
    Hoare (pubkeyLookup key >>= initiationAfterLookup msg e ck hash) (Account holders cs loans) (Acquired holders cs loans) := by
  apply hoare_bind _ _ (show Hoare (pubkeyLookup key) (Account holders cs loans) (Acquired holders cs loans) from ?_)
  · exact fun peer => afterLookup_result msg e ck hash peer
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run
    cases result with
    | none => exact hi.pubkey_none key a b run
    | some pid =>
      obtain ⟨d,p,_,_,_,account⟩ := hi.pubkey key a b run
      exact ⟨⟨d.ifindex,pid,p.internalId⟩,rfl,account⟩

theorem initiation (msg : List UInt8) :
    Hoare (consumeInitiation msg) (Account holders cs loans) (Acquired holders cs loans) := by
  rw [consumeInitiation_factor]
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (loan_bind_head pubkeyLookup; exact lookup_then _ _ _ _ _)
    | (index_material_head initiationOut; exact out_none)
    | (index_material_head invariant; exact stop _)
    | (index_material_head Bind.bind; apply step)
    | (index_material_head getDev; exact store getDev_sameWGStore)
    | loan_crypto (Account holders cs loans)
    | material_component
    | material_intro
    | material_reduce
    | (index_material_head ite; split)
    | material_match


end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
