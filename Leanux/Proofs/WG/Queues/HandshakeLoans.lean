import Leanux.Proofs.WG.AllowedIps.RoutingAcquire
import Leanux.Proofs.WG.Queues.HolderDecrypt
import Leanux.Proofs.WG.Queues.HolderEncryptFrames

/-! Actual handshake acquisitions carry one source-owned peer reservation.
The failure continuation pays that occurrence; success leaves it charged. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

def Inv (cs : Ledger) (loans : Reservations) (w : WGWorld) :=
  CarrierState cs loans w ∧ StableRx cs w

def Result (cs : Ledger) (loans : Reservations) (result : Option PeerId) (w : WGWorld) : Prop :=
  match result with
  | none => Inv cs loans w
  | some pid => ∃ o : Owner, o.slot=pid ∧ Inv cs (o::loans) w

theorem loan_carriers (hi : CarrierState cs loans w) (loan : Loan w result v)
    (keys : KeyEffect NoPromotion w v) : DecryptCarrier.Prepared cs loans result v := by
  cases result with
  | none => exact ⟨inventory_view hi.inventory loan.2,queueOwners_view hi.queues loan.1,
      protected_view hi.funded loan.1,keys.rxCompatible loan.2 hi.keys.1,
      keys.currentsCompatible hi.keys.2 (fun _ _ h => h.elim)⟩
  | some pid =>
    obtain ⟨d,p,hd,hp,positive,funded⟩ := loan_protected loan hi.funded
    exact ⟨⟨d.ifindex,pid,p.internalId⟩,rfl,inventory_view hi.inventory (loan_rx loan),
      queueOwners_base hi.queues (loan_base loan),funded,
      keys.rxCompatible (loan_rx loan) hi.keys.1,
      keys.currentsCompatible hi.keys.2 (fun _ _ h => h.elim)⟩

theorem indexLookup_result (kinds : List IndexKind) (index : Nat)
    (hi : Inv cs loans w) (a b : Ambient)
    (run : ((indexLookup kinds index).run w).run a=.ok ((entry,v),b)) :
    Result cs loans (entry.map Prod.snd) v := by
  have loan := (hoare_iff_run_ambient _ _ _).mp (indexLookup_loan kinds index w)
    w a entry v b rfl run
  have state := loan_carriers hi.1 loan
    ((KeyEffects.iff_run_ambient _ _).mp (indexLookup_keyEffect kinds index) w a entry v b run)
  have stable := hi.2.view ((ProjectedAction.iff_run_ambient _ _ _).mp
    (stable_indexLookup kinds index) w a entry v b run)
  cases entry with
  | none => exact ⟨state,stable⟩
  | some entry =>
    obtain ⟨o,slot,state⟩ := state
    exact ⟨o,slot,state,stable⟩

theorem payment (o : Owner) : Hoare (peerPut (some o.slot))
    (Inv cs (o::loans)) (fun _ => Inv cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a u v b hi run
  cases u
  exact reservation_payment_stable hi.1 hi.2 a b run

private theorem view_spec (action : WG.M α) (same : SameView DecryptCarrier.decryptView action) :
    Preserves (Inv cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  exact ⟨hi.1.view (congrArg Prod.fst frame),hi.2.view (congrArg Prod.snd frame)⟩

private theorem store (action : WG.M α) (same : SameWGStore action) :
    Preserves (Inv cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  exact ⟨hi.1.kernel frame,hi.2.kernel frame⟩

private theorem update (pid : PeerId) (f : Peer → Peer)
    (fields : ∀ p, (p.internalId,p.refcount,p.rxQueue,p.keypairCurrent,p.napiScheduled) =
      ((f p).internalId,(f p).refcount,(f p).rxQueue,(f p).keypairCurrent,(f p).napiScheduled)) :
    Preserves (Inv cs loans) (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply view_spec
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,c,getter,write⟩ := run
  obtain ⟨rfl,rfl,d,hd,hp⟩ := getPeer_normal pid w read p a c getter
  cases write
  have ff := fields p
  simp only [Prod.mk.injEq] at ff
  unfold DecryptCarrier.decryptView carrierView keyView keyWords currentCells currentCell
  unfold peerView rxView stableView RxRing.nativeCell
  simp only [hd,Option.map_some,Option.bind_some]
  rcases ff with ⟨stamp,count,queue,current,napi⟩
  have peers : (fun q : PeerId => (d.peers.insert pid (f p))[q]?.map
      (fun p : Peer => (p.internalId,p.refcount,p.rxQueue))) =
      (fun q : PeerId => d.peers[q]?.map (fun p : Peer => (p.internalId,p.refcount,p.rxQueue))) := by
    funext q
    by_cases same : pid=q
    · subst q; simp only [Std.TreeMap.getElem?_insert_self,hp,Option.map_some,←stamp,←count,←queue]
    · simp only [Std.TreeMap.getElem?_insert,Std.LawfulEqOrd.compare_eq_iff_eq,ite_eq_right same]
  have currents : (fun q : PeerId => (d.peers.insert pid (f p))[q]?.map (fun p : Peer => (p.internalId,p.keypairCurrent))) =
      (fun q : PeerId => d.peers[q]?.map (fun p : Peer => (p.internalId,p.keypairCurrent))) := by
    funext q
    by_cases same : pid=q
    · subst q; simp only [Std.TreeMap.getElem?_insert_self,hp,Option.map_some,←stamp,←current]
    · simp only [Std.TreeMap.getElem?_insert,Std.LawfulEqOrd.compare_eq_iff_eq,ite_eq_right same]
  have napiFrame : (fun q : PeerId => (d.peers.insert pid (f p))[q]?.map (fun p : Peer => (p.rxQueue,p.napiScheduled))) =
      (fun q : PeerId => d.peers[q]?.map (fun p : Peer => (p.rxQueue,p.napiScheduled))) := by
    funext q
    by_cases same : pid=q
    · subst q; simp only [Std.TreeMap.getElem?_insert_self,hp,Option.map_some,←queue,←napi]
    · simp only [Std.TreeMap.getElem?_insert,Std.LawfulEqOrd.compare_eq_iff_eq,ite_eq_right same]
  simp only [rxView,hd,Option.map_some,Option.bind_some,peers,currents,napiFrame]

private theorem step {P : WGWorld → Prop} {Q : α → WGWorld → Prop}
    (action : WG.M β) (ha : Preserves P action) (tail : β → WG.M α)
    (ht : ∀ x, Hoare (tail x) P Q) : Hoare (action >>= tail) P Q :=
  hoare_bind _ _ ha ht

private theorem update_step (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (fields : ∀ p, (p.internalId,p.refcount,p.rxQueue,p.keypairCurrent,p.napiScheduled) =
      ((f p).internalId,(f p).refcount,(f p).rxQueue,(f p).keypairCurrent,(f p).napiScheduled))
    (ht : ∀ x, Hoare (tail x) (Inv cs loans) Q) :
    Hoare (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) (Inv cs loans) Q := by
  simpa only [bind_assoc] using step _ (update pid f fields) tail ht

def responseTail (msg : List UInt8) (identity : StaticIdentity) (pid : PeerId) : WG.M (Option PeerId) := do
  let fail : WG.M (Option PeerId) := do
    peerPut (some pid)
    return none
  let p ← getPeer pid
  let state := p.handshakeState
  if ← branch .crespNotCreatedInitiation (state != HANDSHAKE_CREATED_INITIATION) then return ← fail
  let eph := (msg.drop 12).take 32
  let (ck,h) ← messageEphemeral true eph p.chainingKey p.hash
  let ee ← mixDh false ck p.ephemeralPrivate eph
  if ← branch .crespEeFailed ee.isNone then return ← fail
  let some (ck,_) := ee | invariant "unreachable"
  let se ← mixDh false ck identity.staticPrivate eph
  if ← branch .crespSeFailed se.isNone then return ← fail
  let some (ck,_) := se | invariant "unreachable"
  let outs ← kdf true true ck p.presharedKey
  let (ck,tempHash,key) := (← kdfOut outs 0,← kdfOut outs 1,← kdfOut outs 2)
  let h := noiseHash (h ++ tempHash)
  let dec ← messageDecrypt ((msg.drop 44).take 16) key h
  if ← branch .crespDecryptFailed dec.isNone then return ← fail
  let some (_,h) := dec | invariant "unreachable"
  if ← branch .crespStateChanged ((← getPeer pid).handshakeState != state) then return ← fail
  setPeer pid {(←getPeer pid) with remoteEphemeral := eph,hash:=h,chainingKey:=ck, remoteIndex:=u32le msg 4,handshakeState:=HANDSHAKE_CONSUMED_RESPONSE}
  return some pid

theorem consumeResponse_factor (msg : List UInt8) : consumeResponse msg = (do
    let identity := (← getDev).staticIdentity
    if ← branch .crespNoIdentity !identity.hasIdentity then return none
    let entry ← indexLookup [.handshake] (u32le msg 8)
    if ← branch .crespNoHandshake entry.isNone then return none
    let some (IndexOwner.handshake _,pid) := entry | invariant "a keypair entry under the handshake mask"
    responseTail msg identity pid) := by
  rfl

private theorem failed (o : Owner) : Hoare (do peerPut (some o.slot); pure none)
    (Inv cs (o::loans)) (Result cs loans) := by
  apply hoare_bind _ _ (payment o)
  intro u
  apply hoare_consequence (hoare_pure none (Inv cs loans))
  · exact fun _ h => h
  · intro result w h
    rcases h with ⟨rfl,h⟩
    exact h

private theorem succeeded (o : Owner) : Hoare (pure (some o.slot) : WG.M (Option PeerId))
    (Inv cs (o::loans)) (Result cs loans) := by
  apply hoare_consequence (hoare_pure (some o.slot) (Inv cs (o::loans)))
  · exact fun _ h => h
  · intro result w h
    rcases h with ⟨rfl,h⟩
    exact ⟨o,rfl,h⟩

open Lean Meta Elab Tactic in
elab "loan_update_head" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  unless (target.isAppOf ``Hoare || target.isAppOf ``Triple) && args.size ≥ 3 do
    throwError "not a Hoare contract"
  let action := args[args.size-3]!.consumeMData
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let args := action.getAppArgs
  unless args.size ≥ 2 && args[args.size-2]!.consumeMData.isAppOf ``getPeer do
    throwError "not a peer read"
  let .lam _ _ body _ := args.back!.consumeMData | throwError "not a continuation"
  let body := body.consumeMData
  unless body.isAppOf ``Bind.bind do throwError "not a following bind"
  let next := body.getAppArgs
  unless next.size ≥ 2 && next[next.size-2]!.consumeMData.isAppOf ``setPeer do
    throwError "not a fresh peer update"

open Lean Meta Elab Tactic in
elab "loan_bind_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  unless (target.isAppOf ``Hoare || target.isAppOf ``Triple) && args.size ≥ 3 do
    throwError "not a Hoare contract"
  let action := args[args.size-3]!.consumeMData
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let args := action.getAppArgs
  unless args.size ≥ 2 do throwError "missing bind operands"
  let name ← realizeGlobalConstNoOverloadWithInfo wanted
  unless args[args.size-2]!.consumeMData.isAppOf name do throwError "different first action"

private theorem stop (why : String) : Hoare (invariant why : WG.M α) P Q := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  cases run

private theorem getter (P : WGWorld → Prop) (pid : PeerId) : Preserves P (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  exact (getPeer_normal pid w v p a b run).1 ▸ hi

macro "loan_crypto " P:term : tactic => `(tactic| first
  | (index_material_head messageEphemeral; exact (messageEphemeral_sameWGWorld _ _ _ _).wp $P)
  | (index_material_head mixDh; exact (mixDh_sameWGWorld _ _ _ _).wp $P)
  | (index_material_head messageDecrypt; exact (messageDecrypt_sameWGWorld _ _ _).wp $P)
  | (index_material_head kdf; exact (Framing.kdf_sameWGWorld _ _ _ _).wp $P)
  | (index_material_head kdfOut; exact (Framing.kdfOut_sameWGWorld _ _).wp $P))

theorem responseTail_result (msg : List UInt8) (identity : StaticIdentity) (o : Owner) :
    Hoare (responseTail msg identity o.slot) (Inv cs (o::loans)) (Result cs loans) := by
  unfold responseTail
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (loan_update_head
       apply update_step
       · intro p; rfl
       intro x)
    | (loan_bind_head peerPut; exact failed o)
    | (index_material_head invariant; exact stop _)
    | (index_material_head Pure.pure; first | exact succeeded o | exact preserves_pure _)
    | (index_material_head Bind.bind; apply step)
    | (index_material_head getPeer; exact getter _ _)
    | loan_crypto (Inv cs (o::loans))
    | material_component
    | material_intro
    | material_reduce
    | (index_material_head ite; split)
    | material_match

/-- Normal None repays the actual lookup reference; Some retains it as one
named loan. No successful-acquisition or positive-credit input is assumed. -/
theorem consumeResponse_result (msg : List UInt8) (hi : Inv cs loans w) (a b : Ambient)
    (run : ((consumeResponse msg).run w).run a=.ok ((result,v),b)) :
    Result cs loans result v := by
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
    have acquiredInv := indexLookup_result [.handshake] (u32le msg 8) hi _ e lookup
    cases entry with
    | none =>
      simp only [StateT.run_bind,branch_run,CounterWindow.except_ok_bind,Option.isNone_none,ite_true] at rest
      cases rest
      exact acquiredInv
    | some entry =>
      obtain ⟨owner,pid⟩ := entry
      simp only [StateT.run_bind,branch_run,CounterWindow.except_ok_bind,Option.isNone_some,
        Bool.false_eq_true,ite_false] at rest
      cases owner with
      | keypair id => cases rest
      | handshake id =>
        obtain ⟨o,slot,acquiredInv⟩ := acquiredInv
        exact (hoare_iff_run_ambient _ _ _).mp (responseTail_result msg d.staticIdentity o)
          acquired _ result v b acquiredInv (by simpa only [slot] using rest)

private theorem pubkey_views (key : Key) : SameView (fun w => (stableView w,keyView w)) (pubkeyLookup key) := by
  apply SameView.of_wp
  intro initial
  let P := fun w => (stableView w,keyView w)=initial
  have read : Preserves P getDev := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a d v b hi run
    exact (DecryptCarrier.getDev_current a b run).1 ▸ hi
  have borrow (word : Option PeerId) : Preserves P (peerGetMaybeZero word) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run
    have stable := (ProjectedAction.iff_run_ambient _ _ _).mp (stable_peerGetMaybeZero word) w a result v b run
    have keys := keyView_affiliation ((ProjectedAction.iff_run_ambient _ _ _).mp
      (Affiliation.peerGetMaybeZero_view word) w a result v b run)
    exact (Prod.ext stable keys).trans hi
  unfold pubkeyLookup
  exact preserves_bind read (fun d => preserves_bind (hoare_liftAmbient (AmbientM.branch _ _) P)
    (fun _ => borrow _))

theorem pubkeyLookup_result (key : Key) (hi : Inv cs loans w) (a b : Ambient)
    (run : ((pubkeyLookup key).run w).run a=.ok ((result,v),b)) : Result cs loans result v := by
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (Leanux.Proofs.WG.AllowedIps.pubkeyLookup_borrowed_spec key (wgStoreView w)) w a result v b rfl run
  have views := (ProjectedAction.iff_run_ambient _ _ _).mp (pubkey_views key) w a result v b run
  have loan : Loan w result v := by
    cases result with
    | none =>
      have dev : v.dev=w.dev := congrArg WGStoreView.dev borrowed
      exact ⟨by simp only [peerView,dev],by simp only [rxView,dev]⟩
    | some pid =>
      obtain ⟨d,p,hd,hp,pos,eq⟩ := borrowed
      have dev : v.dev=some {d with peers:=d.peers.insert pid {p with refcount:=p.refcount+1}} :=
        congrArg WGStoreView.dev eq
      change w.dev=some d at hd
      exact ⟨d,p,hd,hp,pos,by simp only [peerView,creditWorld,dev,Option.map_some,Option.bind_some],
        by simp only [rxView,dev,hd,Option.map_some,Option.bind_some]⟩
  have state := loan_carriers hi.1 loan (keyEffect_of_view (congrArg Prod.snd views))
  have stable := hi.2.view (congrArg Prod.fst views)
  cases result with
  | none => exact ⟨state,stable⟩
  | some pid => obtain ⟨o,slot,state⟩ := state; exact ⟨o,slot,state,stable⟩

private theorem maybe_frame (word : Option PeerId) (initial) :
    Preserves (Frame initial) (peerGetMaybeZero word) := by
  unfold peerGetMaybeZero refcountIncNotZero
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,unsupported,invariant]
  repeat' holder_work_step initial

private theorem word_frame (owner : IndexOwner) (word : Option PeerId) (initial) :
    Preserves (Frame initial) (owner.setPeerWord word) := by
  cases owner <;> unfold IndexOwner.setPeerWord
  all_goals repeat' holder_work_step initial

private theorem acquire_frame (owner : IndexOwner) (initial) :
    Preserves (Frame initial) (Affiliation.acquireOwner owner) := by
  unfold Affiliation.acquireOwner
  apply preserves_bind (indexOwner_peerWord_preserves owner (Frame initial))
  intro word
  exact preserves_bind (maybe_frame word initial) (fun result =>
    preserves_bind (word_frame owner result initial) (fun _ => preserves_pure _))

private theorem lookup_frame (kinds : List IndexKind) (index : Nat) (initial) :
    Preserves (Frame initial) (indexLookup kinds index) := by
  rw [←Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head Affiliation.acquireOwner; exact acquire_frame _ initial)
    | (rx_retention_head liftIndex
       apply hoare_liftIndex
       intro w d table hi hd
       exact hi.trans (by constructor <;> first | (simp [passiveView,sendView,hd]) |
         (intro q xs h; simpa [handoffTxView,hd] using h)))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Frame initial)
       intro e state
       change Preserves (Frame initial) _)
    | holder_work_step initial

private theorem pubkey_frame (key : Key) (initial) : Preserves (Frame initial) (pubkeyLookup key) := by
  unfold pubkeyLookup
  simp only [branch]
  repeat' first
    | (rx_retention_head peerGetMaybeZero; exact maybe_frame _ initial)
    | holder_work_step initial

theorem consumeResponse_frame (msg : List UInt8) (initial) :
    Preserves (Frame initial) (consumeResponse msg) := by
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact lookup_frame _ _ initial)
    | (rx_retention_head peerPut; exact HolderWorkFrames.peerPut_frame _ initial)
    | receive_crypto (Frame initial)
    | holder_work_step initial

def FundedResult (holders : DurableHolders) (cs : Ledger) (loans : Reservations)
    (result : Option PeerId) (w : WGWorld) : Prop :=
  match result with
  | none => holders.Funded cs loans w ∧ StableRx cs w
  | some pid => ∃ o : Owner, o.slot=pid ∧ holders.Funded cs (o::loans) w ∧ StableRx cs w

private theorem funded_result {holders : DurableHolders} (hi : holders.Aligned w)
    (frame : Frame w v) (result : Result cs (holders.owners ++ loans) outcome v) :
    FundedResult holders cs loans outcome v := by
  cases outcome with
  | none => exact ⟨⟨hi.frame frame,result.1⟩,result.2⟩
  | some pid =>
    obtain ⟨o,slot,state,stable⟩ := result
    exact ⟨o,slot,⟨hi.frame frame,WorkReservations.carrier_loans_perm state List.perm_middle.symm⟩,stable⟩

theorem consumeResponse_funded (msg : List UInt8) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((consumeResponse msg).run w).run a=.ok ((result,v),b)) :
    FundedResult holders cs loans result v :=
  funded_result hi.aligned
    ((hoare_iff_run_ambient _ _ _).mp (consumeResponse_frame msg w) w a result v b (Frame.refl w) run)
    (consumeResponse_result msg ⟨hi.carriers,stable⟩ a b run)

def initiationOut (peer ret : Option PeerId) : WG.M (Option PeerId) := do
  if ← branch .consumeFailedPut ret.isNone then peerPut peer
  return ret

def initiationTail (msg e ck hash : List UInt8) (peer : Option PeerId) (pid : PeerId) : WG.M (Option PeerId) := do
  let ss ← mixPrecomputedDh ck (← getPeer pid).precomputedStaticStatic
  if ← branch .consumeSsFailed ss.isNone then return ← initiationOut peer none
  let some (ckSs, key) := ss | invariant "unreachable"
  let ts ← messageDecrypt ((msg.drop 88).take 28) key hash
  if ← branch .consumeTimestampFailed ts.isNone then return ← initiationOut peer none
  let some (t, hashT) := ts | invariant "unreachable"
  let p ← getPeer pid
  let replay := memcmp t p.latestTimestamp != .gt
  -- `(s64)last_initiation_consumption + NSEC_PER_SEC / INITIATIONS_PER_SECOND
  -- > (s64)ktime_get_coarse_boottime_ns()`, computed before the test
  let floodLhs : Int64 := p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64
  let now ← hiddenClock64 .floodNow
  if ← WG.orM (branch .consumeReplay replay) (branchCmp .consumeFlood (floodLhs > now) floodLhs.toInt now.toInt) then
    return ← initiationOut peer none
  -- Success! Copy everything to peer
  setPeer pid { (← getPeer pid) with remoteEphemeral := e }
  if ← branch .consumeNewerTimestamp (memcmp t p.latestTimestamp == .gt) then
    setPeer pid { (← getPeer pid) with latestTimestamp := t }
  setPeer pid { (← getPeer pid) with hash := hashT, chainingKey := ckSs, remoteIndex := u32le msg 4 }
  -- `(s64)(last_initiation_consumption - (initiation_consumption = now)) < 0`
  let consumption ← hiddenClock64 .consumptionNow
  let last := (← getPeer pid).lastInitiationConsumption
  let diff : Int64 := last - consumption
  if ← branchCmp .consumeLaterTime (diff < 0) diff.toInt 0 then
    setPeer pid { (← getPeer pid) with lastInitiationConsumption := consumption }
  setPeer pid { (← getPeer pid) with handshakeState := HANDSHAKE_CONSUMED_INITIATION }
  initiationOut peer (some pid)

def initiationAfterLookup (msg e ck hash : List UInt8) (peer : Option PeerId) : WG.M (Option PeerId) := do
  if ← branch .consumeNoPeer peer.isNone then return ← initiationOut none none
  let some pid := peer | invariant "unreachable"
  initiationTail msg e ck hash peer pid

theorem consumeInitiation_factor (msg : List UInt8) : consumeInitiation msg = (do
  let identity := (← getDev).staticIdentity
  if ← branch .consumeNoIdentity !identity.hasIdentity then return ← initiationOut none none
  -- handshake_init: the precomputed initial chaining key and hash
  let hash := noiseHash (handshakeInitHash ++ identity.staticPublic)
  let e := (msg.drop 8).take 32
  let (ck, hash) ← messageEphemeral true e handshakeInitChainingKey hash
  let es ← mixDh true ck identity.staticPrivate e
  if ← branch .consumeEsFailed es.isNone then return ← initiationOut none none
  let some (ck, key) := es | invariant "unreachable"
  let st ← messageDecrypt ((msg.drop 40).take 48) key hash
  if ← branch .consumeStaticFailed st.isNone then return ← initiationOut none none
  let some (s, hash) := st | invariant "unreachable"
  let peer ← pubkeyLookup s
  initiationAfterLookup msg e ck hash peer) := by
  rfl

private theorem out_failed (o : Owner) : Hoare (initiationOut (some o.slot) none)
    (Inv cs (o::loans)) (Result cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  change ((do peerPut (some o.slot); pure none : WG.M (Option PeerId)).run w).run
    (CounterWindow.record a .consumeFailedPut true) = .ok ((result,v),b) at run
  exact (hoare_iff_run_ambient _ _ _).mp (failed o) w _ result v b hi run

private theorem out_success (o : Owner) : Hoare (initiationOut (some o.slot) (some o.slot))
    (Inv cs (o::loans)) (Result cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  change Except.ok ((some o.slot,w),CounterWindow.record a .consumeFailedPut false) =
    .ok ((result,v),b) at run
  cases run
  exact ⟨o,rfl,hi⟩

private theorem out_none : Hoare (initiationOut none none) (Inv cs loans) (Result cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  change Except.ok ((none,w),CounterWindow.record (CounterWindow.record a .consumeFailedPut true) .peerPutNull true) =
    .ok ((result,v),b) at run
  cases run
  exact hi

theorem initiationTail_result (msg e ck hash : List UInt8) (o : Owner) :
    Hoare (initiationTail msg e ck hash (some o.slot) o.slot) (Inv cs (o::loans)) (Result cs loans) := by
  unfold initiationTail WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (loan_update_head
       apply update_step
       · intro p; rfl
       intro x)
    | (index_material_head initiationOut; first | exact out_failed o | exact out_success o)
    | (index_material_head invariant; exact stop _)
    | (index_material_head Pure.pure; first | exact succeeded o | exact preserves_pure _)
    | (index_material_head Bind.bind; apply step)
    | (index_material_head getPeer; exact getter _ _)
    | (index_material_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp (Inv cs (o::loans)))
    | loan_crypto (Inv cs (o::loans))
    | material_component
    | material_intro
    | material_reduce
    | (index_material_head ite; split)
    | material_match

private theorem afterLookup_result (msg e ck hash : List UInt8) (peer : Option PeerId) :
    Hoare (initiationAfterLookup msg e ck hash peer) (Result cs loans peer) (Result cs loans) := by
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
    exact (hoare_iff_run_ambient _ _ _).mp (initiationTail_result msg e ck hash o)
      w _ result v b hi (by simpa only [slot] using run)

private theorem lookup_then (key : Key) (msg e ck hash : List UInt8) :
    Hoare (pubkeyLookup key >>= initiationAfterLookup msg e ck hash) (Inv cs loans) (Result cs loans) := by
  apply hoare_bind _ _ (show Hoare (pubkeyLookup key) (Inv cs loans) (Result cs loans) from ?_)
  · exact fun peer => afterLookup_result msg e ck hash peer
  · apply (hoare_iff_run_ambient _ _ _).mpr
    exact fun w a result v b hi run => pubkeyLookup_result key hi a b run

theorem consumeInitiation_spec (msg : List UInt8) :
    Hoare (consumeInitiation msg) (Inv cs loans) (Result cs loans) := by
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
    | (index_material_head getDev; exact store _ getDev_sameWGStore)
    | loan_crypto (Inv cs loans)
    | material_component
    | material_intro
    | material_reduce
    | (index_material_head ite; split)
    | material_match

theorem consumeInitiation_frame (msg : List UInt8) (initial) :
    Preserves (Frame initial) (consumeInitiation msg) := by
  unfold consumeInitiation WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head pubkeyLookup; exact pubkey_frame _ initial)
    | (rx_retention_head peerPut; exact HolderWorkFrames.peerPut_frame _ initial)
    | receive_crypto (Frame initial)
    | (rx_retention_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
    | holder_work_step initial

theorem consumeInitiation_funded (msg : List UInt8) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((consumeInitiation msg).run w).run a=.ok ((result,v),b)) :
    FundedResult holders cs loans result v :=
  funded_result hi.aligned
    ((hoare_iff_run_ambient _ _ _).mp (consumeInitiation_frame msg w) w a result v b (Frame.refl w) run)
    ((hoare_iff_run_ambient _ _ _).mp (consumeInitiation_spec msg) w a result v b ⟨hi.carriers,stable⟩ run)

/-- Normal execution of the original lifetime observer carries the same
source-acquired loan. This is an endpoint contract, not a history-safety claim. -/
theorem consumeInitiation_observed (msg : List UInt8) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (history : List LifetimeEvent) (a b : Ambient)
    (run : (runStatePrefix (consumeInitiationPrefix msg) w a history).1 = .ok ((result,v),b)) :
    FundedResult holders cs loans result v :=
  consumeInitiation_funded msg hi stable a b
    ((consumeInitiationPrefix_erases msg w a history).symm.trans run)

theorem consumeResponse_observed (msg : List UInt8) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (history : List LifetimeEvent) (a b : Ambient)
    (run : (runStatePrefix (consumeResponsePrefix msg) w a history).1 = .ok ((result,v),b)) :
    FundedResult holders cs loans result v :=
  consumeResponse_funded msg hi stable a b
    ((consumeResponsePrefix_erases msg w a history).symm.trans run)

end Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans
