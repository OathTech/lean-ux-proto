import Leanux.Proofs.WG.AuthenticatedEffects.InitiationFront

/-! A failed initiation repays the reference it actually acquired. Positivity
comes from the original lookup, so cleanup cannot delete a peer. The projection
retains complete peer records pointwise rather than TreeMap representation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans
open Leanux.Proofs.WG.Cookies
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def initiationSuccess (msg e ck hash t : Key) (peer : Option PeerId) (pid : PeerId) (p : Peer) :
    WG.M (Option PeerId) := do
  setPeer pid { (← getPeer pid) with remoteEphemeral := e }
  if ← branch .consumeNewerTimestamp (memcmp t p.latestTimestamp == .gt) then
    setPeer pid { (← getPeer pid) with latestTimestamp := t }
  setPeer pid { (← getPeer pid) with hash := hash, chainingKey := ck, remoteIndex := u32le msg 4 }
  let consumption ← hiddenClock64 .consumptionNow
  let last := (← getPeer pid).lastInitiationConsumption
  let diff : Int64 := last - consumption
  if ← branchCmp .consumeLaterTime (diff < 0) diff.toInt 0 then
    setPeer pid { (← getPeer pid) with lastInitiationConsumption := consumption }
  setPeer pid { (← getPeer pid) with handshakeState := HANDSHAKE_CONSUMED_INITIATION }
  initiationOut peer (some pid)

theorem initiationTail_success_factor (msg e ck hash : Key) (peer : Option PeerId) (pid : PeerId) :
    initiationTail msg e ck hash peer pid = (do
      let ss ← mixPrecomputedDh ck (← getPeer pid).precomputedStaticStatic
      if ← branch .consumeSsFailed ss.isNone then return ← initiationOut peer none
      let some (ckSs,key) := ss | invariant "unreachable"
      let ts ← messageDecrypt ((msg.drop 88).take 28) key hash
      if ← branch .consumeTimestampFailed ts.isNone then return ← initiationOut peer none
      let some (t,hashT) := ts | invariant "unreachable"
      let p ← getPeer pid
      let replay := memcmp t p.latestTimestamp != .gt
      let floodLhs : Int64 := p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64
      let now ← hiddenClock64 .floodNow
      if ← WG.orM (branch .consumeReplay replay)
          (branchCmp .consumeFlood (floodLhs > now) floodLhs.toInt now.toInt) then
        return ← initiationOut peer none
      initiationSuccess msg e ckSs hashT t peer pid p) := by
  rfl

private theorem arbitrary (action : WG.M α) : Preserves (fun _ => True) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  trivial

private theorem chain {α β : Type} (P : WGWorld → Prop) (Q : β → WGWorld → Prop)
    (action : WG.M α) (next : α → WG.M β) (ha : Preserves P action)
    (tail : ∀ x, Hoare (next x) P Q) : Hoare (action >>= next) P Q :=
  hoare_bind action next ha tail

theorem initiationSuccess_some (msg e ck hash t : Key) (peer : Option PeerId)
    (pid : PeerId) (p : Peer) :
    Hoare (initiationSuccess msg e ck hash t peer pid p) (fun _ => True)
      (fun result _ => result = some pid) := by
  have out : Hoare (initiationOut peer (some pid)) (fun _ => True)
      (fun result _ => result = some pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run
    change Except.ok ((some pid,w),record a .consumeFailedPut false) = _ at run
    cases run
    rfl
  unfold initiationSuccess
  repeat' first
    | exact out
    | with_reducible apply chain (fun _ => True)
    | exact arbitrary _
    | (session_origin_intro_forall; try dsimp only)
    | split

private def RefusalRestores (initial : WGStoreView) (result : Option PeerId) (w : WGWorld) : Prop :=
  result = none → PeerBorrow.view w = (PeerBorrow.outsidePeers initial,PeerBorrow.resident initial)

private theorem out_restores (peer : Option PeerId) (initial : WGStoreView) :
    Hoare (initiationOut peer none) (fun w => PeerBorrow.Borrowed initial peer (wgStoreView w))
      (RefusalRestores initial) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b borrowed run _
  change ((peerPut peer >>= fun _ => pure (none : Option PeerId)).run w).run
    (record a .consumeFailedPut true) = _ at run
  rw [native_bind_run] at run
  cases paid : ((peerPut peer).run w).run (record a .consumeFailedPut true) with
  | error err => simp [paid] at run
  | ok out =>
    rcases out with ⟨⟨doneUnit,z⟩,c⟩
    have restored := (hoare_iff_run_ambient _ _ _).mp (PeerBorrow.repay_spec peer initial)
      w _ doneUnit z c borrowed paid
    rw [paid] at run
    cases run
    exact restored

theorem initiationTail_refusal_restores (msg e ck hash : Key) (pid : PeerId) (initial : WGStoreView) :
    Hoare (initiationTail msg e ck hash (some pid) pid)
      (fun w => PeerBorrow.Borrowed initial (some pid) (wgStoreView w)) (RefusalRestores initial) := by
  let P := fun w => PeerBorrow.Borrowed initial (some pid) (wgStoreView w)
  have read (q : PeerId) : Preserves P (getPeer q) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi run
    rw [(Leanux.Proofs.WG.Queues.getPeer_normal q w v p a b run).1]
    exact hi
  have success (ck hash t : Key) (p : Peer) :
      Hoare (initiationSuccess msg e ck hash t (some pid) pid p) P (RefusalRestores initial) := by
    apply hoare_consequence (initiationSuccess_some msg e ck hash t (some pid) pid p)
    · exact fun _ _ => True.intro
    · intro result w same none
      rw [same] at none
      cases none
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : WG.M α) :=
    hoare_liftAmbient action P
  have precomputed (ck key : Key) : Preserves P (mixPrecomputedDh ck key) :=
    (mixPrecomputedDh_sameWGWorld ck key).wp P
  have decrypt (sealed key hash : Key) : Preserves P (messageDecrypt sealed key hash) :=
    (messageDecrypt_sameWGWorld sealed key hash).wp P
  have stop (message : String) : Hoare (invariant message : WG.M (Option PeerId)) P (RefusalRestores initial) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run
    cases run
  rw [initiationTail_success_factor]
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,WG.orM]
  repeat' first
    | with_reducible exact success _ _ _ _
    | with_reducible exact out_restores (some pid) initial
    | with_reducible exact stop _
    | with_reducible exact read _
    | with_reducible exact precomputed _ _
    | with_reducible exact decrypt _ _ _
    | with_reducible exact ambient _
    | with_reducible exact preserves_pure _
    | cookie_source_step
    | with_reducible apply chain P
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem initiation_refusal_restores_peers (msg : List UInt8)
    (w v : WGWorld) (a b : Ambient)
    (run : ((consumeInitiation msg).run w).run a = .ok ((none,v),b)) :
    PeerBorrow.view v = PeerBorrow.view w := by
  rw [initiationAuthFront_factor,native_bind_run] at run
  cases front : ((initiationAuthFront msg).run w).run a with
  | error err => simp [front] at run
  | ok out =>
    rcases out with ⟨⟨payload,u⟩,c⟩
    rw [front] at run
    have same := (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
      (initiationAuthFront_same_world msg) w a payload u c front
    change u = w at same
    subst u
    cases payload with
    | none =>
      change Except.ok ((none,w),record (record c .consumeFailedPut true) .peerPutNull true) = _ at run
      cases run
      rfl
    | some payload =>
      rcases payload with ⟨e,ck,s,hash⟩
      dsimp only at run
      rw [native_bind_run] at run
      cases lookup : ((pubkeyLookup s).run w).run c with
      | error err => simp [lookup] at run
      | ok out =>
        rcases out with ⟨⟨peer,q⟩,d⟩
        rw [lookup] at run
        have borrowed := (hoare_iff_run_ambient _ _ _).mp
          (Leanux.Proofs.WG.AllowedIps.pubkeyLookup_borrowed_spec s (wgStoreView w))
          w c peer q d rfl lookup
        cases peer with
        | none =>
          change Except.ok ((none,q),record (record (record d .consumeNoPeer true)
            .consumeFailedPut true) .peerPutNull true) = _ at run
          cases run
          exact congrArg (fun store => (PeerBorrow.outsidePeers store,PeerBorrow.resident store)) borrowed
        | some pid =>
          change ((initiationTail msg e ck hash (some pid) pid).run q).run
            (record d .consumeNoPeer false) = _ at run
          exact (hoare_iff_run_ambient _ _ _).mp
            (initiationTail_refusal_restores msg e ck hash pid (wgStoreView w))
            q _ none v b borrowed run rfl

end Leanux.Proofs.WG.AuthenticatedEffects
