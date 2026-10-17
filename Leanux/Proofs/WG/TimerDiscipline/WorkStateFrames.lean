import Leanux.Proofs.WG.TimerDiscipline.SendWorkerSource
import Leanux.Proofs.WG.Index.Insert

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

private theorem queueWork_setPeer (pid : PeerId) (queue : WorkQueues) (pending : Bool)
    (p : Peer) (flag : p.handshakePending = pending) :
    Ensures (setPeer pid p) (fun g => queueWorkAt g pid = (some queue, some pending))
      (fun _ g => queueWorkAt g pid = (some queue, some pending)) := by
  intro g ambient result final after pre run
  cases run
  cases device : g.dev with
  | none => simp [queueWorkAt, queueWorkKernel, device] at pre
  | some d =>
    have queues : workQueues d = queue := by
      simpa [queueWorkAt, queueWorkKernel, device] using congrArg Prod.fst pre
    simp [queueWorkAt, queueWorkKernel, device, workQueues, flag] at queues ⊢
    exact queues

private theorem queueWork_write (pid : PeerId) (queue : WorkQueues) (pending : Bool)
    (f : Peer → Peer) (same : ∀ p, (f p).handshakePending = p.handshakePending) :
    Ensures (do setPeer pid (f (← getPeer pid)))
      (fun g => queueWorkAt g pid = (some queue, some pending))
      (fun _ g => queueWorkAt g pid = (some queue, some pending)) := by
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid
    (fun g => queueWorkAt g pid = (some queue, some pending)))) ?_
  intro p g ambient result final after pre run
  have flag : p.handshakePending = pending := by
    have observed := congrArg Prod.snd pre.1
    change (peerAt g pid).map Peer.handshakePending = some pending at observed
    simpa only [pre.2, Option.map_some, Option.some.injEq] using observed
  exact queueWork_setPeer pid queue pending (f p) ((same p).trans flag)
    g ambient result final after pre.1 run

theorem indexInsert_queueWorkView (owner : IndexOwner) (pid : PeerId)
    (queue : WorkQueues) (pending : Bool) :
    ⦃fun g => ⌜queueWorkAt g pid = (some queue, some pending)⌝⦄ liftIndex (indexInsert owner)
      ⦃⇓? _ g => ⌜queueWorkAt g pid = (some queue, some pending)⌝⦄ := by
  refine hoare_liftIndex_variant _ _ ?_
  intro g d table pre device
  simpa [queueWorkAt, queueWorkKernel, workQueues, device] using pre

theorem setChain_spec_queue_variant (pid : PeerId) (ck hash : List UInt8)
    (queue : WorkQueues) (pending : Bool) :
    ⦃fun g => ⌜queueWorkAt g pid = (some queue, some pending)⌝⦄
      (noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck hash
      ⦃⇓? _ g => ⌜queueWorkAt g pid = (some queue, some pending)⌝⦄ := by
  exact (ensures_iff _ _ _).mp (queueWork_write pid queue pending
    (fun p => {p with chainingKey := ck, hash}) (fun _ => rfl))

theorem createInitiation_queueWorkView (pid : PeerId) (queue : WorkQueues) (pending : Bool) :
    ⦃fun w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ createInitiation pid
      ⦃⇓? _ w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ := by
  let P : WGWorld → Prop := fun g => queueWorkAt g pid = (some queue, some pending)
  apply (ensures_iff _ _ _).mp
  change Ensures _ P (fun _ => P)
  have hpure : Ensures (pure none : WG.M (Option (List UInt8))) P (fun _ => P) := by
    intro g ambient x g' ambient' hp hr
    cases hr
    exact hp
  have hstop {α : Type} (what : String) (Q : α → WGWorld → Prop) :
      Ensures (invariant what : WG.M α) P Q := by
    intro g ambient x g' ambient' hp hr
    simp [invariant, AmbientM.invariant] at hr
    cases hr
  have hread : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient x g' ambient' hp hr
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P)
      g ambient x g' ambient' hp hr).1
  have hdev : Ensures getDev P (fun _ => P) := by
    intro g ambient x g' ambient' hp hr
    cases hd : g.dev with
    | none =>
      simp [getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      simp [getDev, hd] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact hp
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hhidden (site : HiddenSite) :
      Ensures (hidden site : WG.M (List UInt8)) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hidden site) P)
  have hwrite (f : Peer → Peer)
      (same : ∀ p, (f p).handshakePending = p.handshakePending) :
      Ensures (do setPeer pid (f (← getPeer pid))) P (fun _ => P) :=
    queueWork_write pid queue pending f same
  have hchain (ck hash : List UInt8) :
      Ensures ((noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck hash)
        P (fun _ => P) :=
    hwrite (fun p => {p with chainingKey := ck, hash}) (fun _ => rfl)
  have hderef : Ensures (IndexOwner.peerDeref (.handshake pid)) P (fun _ => P) := by
    unfold IndexOwner.peerDeref IndexOwner.peerWord
    refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
    · refine ensures_bind (Q := fun _ => P) _ _ hread ?_
      intro p g ambient x g' ambient' hp hr
      cases hr
      exact hp
    · intro word
      cases word with
      | none =>
        exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
          (AmbientM.unsupported "entry->peer is NULL: the C dereferences it") P)
      | some target =>
        intro g ambient x g' ambient' hp hr
        cases hr
        exact hp
  have hindex : Ensures (liftIndex (indexInsert (.handshake pid))) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (indexInsert_queueWorkView (.handshake pid) pid queue pending)
  unfold createInitiation
  refine ensures_bind _ _ hdev ?_
  intro d
  refine ensures_bind _ _ (hbranch _ _) ?_
  intro noIdentity
  cases noIdentity with
  | true => exact hpure
  | false =>
    refine ensures_bind _ _ hread ?_
    intro p
    refine ensures_bind _ _ (hchain _ _) ?_
    intro _
    refine ensures_bind _ _ (hhidden _) ?_
    intro secret
    rw [← bind_assoc]
    refine ensures_bind _ _ (hwrite (fun p => {p with ephemeralPrivate := clamp secret})
      (fun _ => rfl)) ?_
    intro _
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (generatePublic_wg_spec P _)) ?_
    intro generated
    rcases generated with ⟨pub, ok⟩
    refine ensures_bind _ _ (hbranch _ _) ?_
    intro noEphemeral
    cases noEphemeral with
    | true => exact hpure
    | false =>
      cases pub with
      | none => exact hstop _ (fun _ => P)
      | some e =>
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (messageEphemeral_wg_spec P _ _ _ _)) ?_
        intro ephemeral
        rcases ephemeral with ⟨ck, hash⟩
        refine ensures_bind _ _ (hchain _ _) ?_
        intro _
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (mixDh_wg_spec P _ _ _ _)) ?_
        intro es
        refine ensures_bind _ _ (hbranch _ _) ?_
        intro esFailed
        cases esFailed with
        | true => exact hpure
        | false =>
          cases es with
          | none => exact hstop _ (fun _ => P)
          | some es =>
            rcases es with ⟨ck, key⟩
            refine ensures_bind _ _ (hchain _ _) ?_
            intro _
            refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (mixPrecomputedDh_wg_spec P _ _)) ?_
            intro ss
            refine ensures_bind _ _ (hbranch _ _) ?_
            intro ssFailed
            cases ssFailed with
            | true => exact hpure
            | false =>
              cases ss with
              | none => exact hstop _ (fun _ => P)
              | some ss =>
                rcases ss with ⟨ck, key⟩
                refine ensures_bind _ _ (hhidden _) ?_
                intro now
                refine ensures_bind _ _ (hchain _ _) ?_
                intro _
                refine ensures_bind _ _ hderef ?_
                intro _
                refine ensures_bind _ _ hindex ?_
                intro index
                rw [← bind_assoc]
                refine ensures_bind _ _ (hwrite
                  (fun p => {p with handshakeState := HANDSHAKE_CREATED_INITIATION})
                  (fun _ => rfl)) ?_
                intro _ g ambient x g' ambient' hp hr
                cases hr
                exact hp

theorem addMacToPacket_queueWorkView (pid : PeerId) (msg : List UInt8) (queue : WorkQueues) (pending : Bool) :
    ⦃fun w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ addMacToPacket pid msg
      ⦃⇓? _ w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ := by
  let P : WGWorld → Prop := fun g => queueWorkAt g pid = (some queue, some pending)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g ambient y g' ambient' hp hr
    cases hr
    exact hp
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) :
      Ensures (branchCmp site value lhs rhs : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branchCmp site value lhs rhs) P)
  have hclock : Ensures (hiddenClock64 .birthdateExpired : WG.M Int64) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hiddenClock64 .birthdateExpired) P)
  have hexpired (birthday : Int64) :
      Ensures (branchExpired .addMacCookieFresh birthday COOKIE_FRESH_SECONDS (!·)) P (fun _ => P) := by
    unfold branchExpired birthdateTest
    rw [bind_assoc]
    refine ensures_bind _ _ hclock ?_
    intro now
    simp only [pure_bind]
    exact hcmp _ _ _ _
  apply (ensures_iff _ _ _).mp
  change Ensures _ P (fun _ => P)
  unfold addMacToPacket
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
  intro p
  refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
  · intro g ambient result final after pre run
    have flag : p.handshakePending = pending := by
      have observed := congrArg Prod.snd pre.1
      change (peerAt g pid).map Peer.handshakePending = some pending at observed
      simpa only [pre.2, Option.map_some, Option.some.injEq] using observed
    exact queueWork_setPeer pid queue pending {p with
      lastMac1Sent := blake2s 16 p.cookieMac1Key (msg.take (msg.length - 32)), haveSentMac1 := true}
      flag g ambient result final after pre.1 run
  · intro _
    refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
    · unfold Leanux.WG.andM
      refine ensures_bind _ _ (hbranch _ _) ?_
      intro valid
      cases valid with
      | false => exact hpure false
      | true => exact hexpired _
    · intro valid
      cases valid <;> exact hpure _

private theorem armTimer_queueWorkView (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : Option UInt64) (queue : WorkQueues) (pending : Bool) :
      Ensures (armTimer pid timer delay caller)
      (fun g => queueWorkAt g pid = (some queue, some pending))
      (fun _ g => queueWorkAt g pid = (some queue, some pending)) := by
  let P : WGWorld → Prop := fun g => queueWorkAt g pid = (some queue, some pending)
  intro g ambient result final after pre run
  cases result
  cases device : g.dev with
  | none => simp [queueWorkAt, queueWorkKernel, device] at pre
  | some d =>
    cases found : d.peers[pid]? with
    | none => simp [queueWorkAt, queueWorkKernel, device, found] at pre
    | some p =>
      have resident : peerAt g pid = some p := by simp [peerAt, device, found]
      have flag : p.handshakePending = pending := by
        simpa [queueWorkAt, queueWorkKernel, device, found] using congrArg Prod.snd pre
      have queues : workQueues d = queue := by
        simpa [queueWorkAt, queueWorkKernel, device] using congrArg Prod.fst pre
      have wheelFrame (entry : WGWorld) (same : entry.dev = some d) (expires clk : UInt64) :
          P (wheelPlacementState entry pid p timer expires clk) := by
        cases placed : TimerWheel.place p timer expires clk <;> cases timer <;>
          simp [P, queueWorkAt, queueWorkKernel, wheelPlacementState, placed, same,
            workQueues, Peer.setTimer, Peer.setWheel] at queues ⊢
        all_goals exact ⟨queues, flag⟩
      cases mode : ambient.armRecords with
      | false =>
        rw [armTimer_off_effect pid timer delay caller g p resident ambient after final mode run]
        exact wheelFrame g device _ _
      | true =>
        cases caller with
        | none =>
          have ambientRead : ((getAmbient : WG.M Ambient).run g).run ambient = .ok ((ambient, g), ambient) := rfl
          have hiddenRead : ((hidden .modTimerArm : WG.M (List UInt8)).run g).run ambient =
              ((AmbientM.hidden .modTimerArm).run ambient >>= fun (bytes, next) => .ok ((bytes, g), next)) := rfl
          simp only [armTimer, StateT.run_bind, StateT.run_get, pure_bind] at run
          rw [ambientRead] at run
          simp only [bind, Except.bind, mode, Bool.not_true, Bool.false_eq_true, ite_false] at run
          change (((hidden .modTimerArm : WG.M (List UInt8)).run g).run ambient >>= _) = _ at run
          rw [hiddenRead] at run
          cases read : (AmbientM.hidden .modTimerArm).run ambient with
          | error err => rw [read] at run; cases run
          | ok out => rw [read] at run; cases out; cases run
        | some caller =>
          by_cases same : p.timer timer = some (caller + delay.toUInt64)
          · obtain ⟨now, unit, _, _, effect⟩ := armTimer_sameExpiry_effect pid timer delay caller
              g p resident same ambient after final mode run
            rw [effect]
            exact pre
          · obtain ⟨now, unit, clk, _, _, effect⟩ := armTimer_changedExpiry_effect pid timer delay caller
              g p resident same ambient after final mode run
            rw [effect]
            exact wheelFrame {recordedArmPrefixState g pid timer now unit with timerClk := some clk} device _ _

theorem modPeerTimer_queueWorkView (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (queue : WorkQueues) (pending : Bool) :
    ⦃fun g => ⌜queueWorkAt g pid = (some queue, some pending)⌝⦄ modPeerTimer site pid timer delay
      ⦃⇓? _ g => ⌜queueWorkAt g pid = (some queue, some pending)⌝⦄ := by
  let P : WGWorld → Prop := fun g => queueWorkAt g pid = (some queue, some pending)
  have callerFrame : Ensures (callerJiffies site) P (fun _ => P) := by
    intro g ambient result final after pre run
    rw [(callerJiffies_input_effect _ g final ambient after result run).1]
    exact pre
  have guardFrame : Ensures (modPeerTimerGuard pid) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [P, queueWorkAt, queueWorkKernel, device] at pre
    | some d =>
      cases found : d.peers[pid]? with
      | none => simp [P, queueWorkAt, queueWorkKernel, device, found] at pre
      | some p =>
        rw [(modPeerTimerGuard_input_effect pid d p found g final ambient after result device run).2.1]
        exact pre
  apply (ensures_iff _ _ _).mp
  unfold modPeerTimer
  refine ensures_bind _ _ callerFrame ?_
  intro caller
  refine ensures_bind _ _ guardFrame ?_
  intro allowed
  cases allowed with
  | false => intro g ambient result final after pre run; cases run; exact pre
  | true =>
    refine ensures_bind _ _ (armTimer_queueWorkView pid timer delay caller queue pending) ?_
    intro _ g ambient result final after pre run; cases run; exact pre

theorem traversal_queueWorkView (pid : PeerId) (queue : WorkQueues) (pending : Bool) :
    ⦃fun g => ⌜queueWorkAt g pid = (some queue, some pending)⌝⦄ timersTraversal pid
      ⦃⇓? _ g => ⌜queueWorkAt g pid = (some queue, some pending)⌝⦄ := by
  let P : WGWorld → Prop := fun g => queueWorkAt g pid = (some queue, some pending)
  apply (ensures_iff _ _ _).mp
  have read : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P)
      g ambient result final after pre run).1
  unfold timersTraversal
  refine ensures_bind _ _ read ?_
  intro peer
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.branchCmp .traversalKeepalive
      (peer.persistentKeepaliveInterval != 0) peer.persistentKeepaliveInterval 0) P)) ?_
  intro enabled
  cases enabled with
  | false =>
    intro g ambient result final after pre run
    cases run
    exact pre
  | true =>
    have mapped := map_result_native_spec (fun _ : Bool => PUnit.unit)
      (modPeerTimer .timerJiffiesTraversal pid .persistentKeepalive (peer.persistentKeepaliveInterval * HZ))
      P (fun _ => P)
      (modPeerTimer_queueWorkView .timerJiffiesTraversal pid .persistentKeepalive (peer.persistentKeepaliveInterval * HZ) queue pending)
    intro g ambient result final after pre run
    obtain ⟨_, _, preserved⟩ := (ensures_iff _ _ _).mpr mapped
      g ambient result final after pre run
    exact preserved

theorem delKeepalive_queueWorkView (pid : PeerId) (queue : WorkQueues) (pending : Bool) :
    ⦃fun g => ⌜queueWorkAt g pid = (some queue, some pending)⌝⦄ timersAnyAuthenticatedPacketSent pid
      ⦃⇓? _ g => ⌜queueWorkAt g pid = (some queue, some pending)⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  exact queueWork_write pid queue pending (fun p => (p.setTimer .sendKeepalive none).setWheel .sendKeepalive none)
    (fun _ => rfl)

theorem initiationArmPrefix_queueWorkView (pid : PeerId) (queue : WorkQueues) (pending : Bool) :
    ⦃fun w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ initiationArmPrefix pid
      ⦃⇓? _ w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ := by
  let P : WGWorld → Prop := fun g => queueWorkAt g pid = (some queue, some pending)
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) := hambient (AmbientM.branch site value)
  have hread : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P) g ambient result final after pre run).1
  have hclock (birthday : Int64) :
      Ensures (branchExpired .initRateLimited birthday REKEY_TIMEOUT (!·)) P (fun _ => P) := by
    simp only [branchExpired, birthdateTest, bind_assoc, pure_bind]
    refine ensures_bind (Q := fun _ => P) _ _ (hambient (AmbientM.hiddenClock64 .birthdateExpired)) ?_
    intro now
    exact hambient (AmbientM.branchCmp _ _ _ _)
  have hstop (message : String) : Ensures (invariant message : WG.M Bool) P (fun _ => P) := by
    intro g ambient result final after pre run; cases run
  have hwrite (now : Int64) : Ensures (do
      let p ← getPeer pid
      setPeer pid {p with lastSentHandshake := now}) P (fun _ => P) :=
    queueWork_write pid queue pending (fun p => {p with lastSentHandshake := now}) (fun _ => rfl)
  have writeBind {α : Type} (now : Int64) (next : WG.M α) (rest : Ensures next P (fun _ => P)) :
      Ensures (do
        let p ← getPeer pid
        setPeer pid {p with lastSentHandshake := now}
        next) P (fun _ => P) := by
    simpa only [bind_assoc] using ensures_bind _ (fun _ => next) (hwrite now) (fun _ => rest)
  have hmac (msg : List UInt8) : Ensures (addMacToPacket pid msg) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (addMacToPacket_queueWorkView pid msg queue pending)
  have hsend (msg : List UInt8) : Ensures (sendBufferToPeer pid msg) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (sendBufferToPeer_queueWorkView pid msg (some queue, some pending))
  have htraversal := (ensures_iff _ _ _).mpr (traversal_queueWorkView pid queue pending)
  have hdel := (ensures_iff _ _ _).mpr (delKeepalive_queueWorkView pid queue pending)
  have hcreate := (ensures_iff _ _ _).mpr (createInitiation_queueWorkView pid queue pending)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (yesFrame : Ensures yes P (fun _ => P)) (noFrame : Ensures no P (fun _ => P)) :
      Ensures (if condition then yes else no) P (fun _ => P) := by split <;> assumption
  apply (ensures_iff _ _ _).mp
  change Ensures _ P (fun _ => P)
  unfold initiationArmPrefix
  refine ensures_bind _ _ hread ?_
  intro peer
  refine ensures_bind _ _ (hclock peer.lastSentHandshake) ?_
  intro limited
  cases limited with
  | true => exact hpure false
  | false =>
    refine ensures_bind _ _ (hambient (AmbientM.hiddenClock64 .initLastSent)) ?_
    intro now
    refine writeBind now _ ?_
    refine ensures_bind _ _ hcreate ?_
    intro created
    cases created
    all_goals
      repeat' first
        | exact hpure _
        | exact hambient _
        | exact hbranch _ _
        | exact hread
        | exact hstop _
        | exact hwrite _
        | exact hmac _
        | exact hsend _
        | exact htraversal
        | exact hdel
        | (apply writeBind)
        | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
        | (refine hif _ _ _ ?_ ?_)

theorem timersHandshakeInitiated_queueWorkView (pid : PeerId) (queue : WorkQueues) (pending : Bool) :
    ⦃fun w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ timersHandshakeInitiated pid
      ⦃⇓? _ w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ := by
  let P : WGWorld → Prop := fun g => queueWorkAt g pid = (some queue, some pending)
  have hpure : Ensures (pure () : WG.M Unit) P (fun _ => P) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hcaller : Ensures (callerJiffies .timerJiffiesHandshakeInitiated) P (fun _ => P) := by
    intro g ambient result final after pre run
    rw [(callerJiffies_input_effect _ g final ambient after result run).1]
    exact pre
  have hguard : Ensures (modPeerTimerGuard pid) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [P, queueWorkAt, queueWorkKernel, device] at pre
    | some d =>
      cases found : d.peers[pid]? with
      | none => simp [P, queueWorkAt, queueWorkKernel, device, found] at pre
      | some p =>
        rw [(modPeerTimerGuard_input_effect pid d p found g final ambient after result device run).2.1]
        exact pre
  apply (ensures_iff _ _ _).mp
  change Ensures _ P (fun _ => P)
  unfold timersHandshakeInitiated
  refine ensures_bind _ _ hcaller ?_
  intro caller
  refine ensures_bind _ _ (jitter_wg_spec P .retransmitJitter) ?_
  intro jitter
  refine ensures_bind _ _ hguard ?_
  intro allowed
  cases allowed with
  | false => exact hpure
  | true => exact armTimer_queueWorkView pid .retransmitHandshake (REKEY_TIMEOUT_TICKS + jitter) caller queue pending

theorem sendHandshakeInitiation_queueWorkView (pid : PeerId) (queue : WorkQueues) (pending : Bool) :
    Ensures (sendHandshakeInitiation pid)
      (fun g => queueWorkAt g pid = (some queue, some pending))
      (fun _ g => queueWorkAt g pid = (some queue, some pending)) := by
  rw [sendInitiation_arm_source]
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (initiationArmPrefix_queueWorkView pid queue pending)) ?_
  intro reached
  cases reached with
  | false => intro g ambient result final after pre run; cases run; exact pre
  | true => exact (ensures_iff _ _ _).mpr (timersHandshakeInitiated_queueWorkView pid queue pending)

private theorem work_frame_of_queueWork_native {α : Type} (action : WG.M α) (pid : PeerId)
    (frame : ∀ (queues : WorkQueues) (pending : Bool),
      ⦃fun w => ⌜queueWorkAt w pid = (some queues, some pending)⌝⦄ action
        ⦃⇓? _ w => ⌜queueWorkAt w pid = (some queues, some pending)⌝⦄)
    (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ action
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w ambient result final after pre run
  cases hd : w.dev with
  | none => simp [workAt, workKernel, hd] at pre
  | some d =>
    have hp : d.peers[pid]?.map Peer.handshakePending = some pending := by
      simpa [workAt, workKernel, hd] using congrArg Prod.snd pre
    have h := (ensures_iff _ _ _).mpr
      (frame (workQueues d) pending) w ambient result final after
        (by simpa [queueWorkAt, queueWorkKernel, workAt, workKernel, hd] using hp) run
    have projected := congrArg (fun x : QueueWorkView => (x.1.map Prod.fst, x.2)) h
    have same : workAt final pid = workAt w pid := by
      simpa [queueWorkAt, queueWorkKernel, workAt, workKernel, workQueues,
        Option.map_map, Function.comp_def, hd, hp] using projected
    exact same.trans pre

/-- Projections retain every prior work-state interface. -/
theorem indexInsert_workView (owner : IndexOwner) (pid : PeerId)
    (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ liftIndex (indexInsert owner)
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork_native (liftIndex (indexInsert owner)) pid
    (indexInsert_queueWorkView owner pid) queue pending

theorem createInitiation_workView (pid : PeerId) (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ createInitiation pid
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork_native (createInitiation pid) pid
    (createInitiation_queueWorkView pid) queue pending

theorem addMacToPacket_workView (pid : PeerId) (msg : List UInt8)
    (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ addMacToPacket pid msg
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork_native (addMacToPacket pid msg) pid
    (addMacToPacket_queueWorkView pid msg) queue pending

theorem modPeerTimer_workView (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ modPeerTimer site pid timer delay
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork_native (modPeerTimer site pid timer delay) pid
    (modPeerTimer_queueWorkView site pid timer delay) queue pending

theorem traversal_workView (pid : PeerId) (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ timersTraversal pid
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork_native (timersTraversal pid) pid
    (traversal_queueWorkView pid) queue pending

theorem delKeepalive_workView (pid : PeerId) (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ timersAnyAuthenticatedPacketSent pid
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork_native (timersAnyAuthenticatedPacketSent pid) pid
    (delKeepalive_queueWorkView pid) queue pending

theorem initiationArmPrefix_workView (pid : PeerId) (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ initiationArmPrefix pid
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork_native (initiationArmPrefix pid) pid
    (initiationArmPrefix_queueWorkView pid) queue pending

theorem timersHandshakeInitiated_workView (pid : PeerId) (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ timersHandshakeInitiated pid
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork_native (timersHandshakeInitiated pid) pid
    (timersHandshakeInitiated_queueWorkView pid) queue pending

theorem sendHandshakeInitiation_workView (pid : PeerId) (queue : List PeerId) (pending : Bool) :
    Ensures (sendHandshakeInitiation pid)
      (fun w => workAt w pid = (some queue, some pending))
      (fun _ w => workAt w pid = (some queue, some pending)) := by
  rw [ensures_iff]
  exact work_frame_of_queueWork_native (sendHandshakeInitiation pid) pid
    (fun queues flag => (ensures_iff _ _ _).mp (sendHandshakeInitiation_queueWorkView pid queues flag)) queue pending

theorem retained_peerPut_workView (pid : PeerId) (identity attempts refs : Nat)
    (queue : List PeerId) (pending : Bool) (retained : 1 < refs) :
    Ensures (peerPut (some pid))
      (fun g => workerAt g pid = some (identity, attempts, refs) ∧
        workAt g pid = (some queue, some pending))
      (fun _ g => workAt g pid = (some queue, some pending)) := by
  intro g ambient result final after pre run
  cases result
  cases hd : g.dev with
  | none => simp [workerAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [workerAt, peerAt, hd, hp] at pre
    | some p =>
      have hv : workerView p = (identity, attempts, refs) := by
        simpa [workerAt, peerAt, hd, hp] using pre.1
      have hr : p.refcount = refs := congrArg (fun x => x.2.2) hv
      have last : p.refcount ≠ 1 := by omega
      have effect := Index.peerPut_exact pid d p hp (by omega) g ambient hd
      simp only [last, ite_false] at effect
      change ∃ observed, Campaign2.observeResult _ = .ok ((), observed) ∧
        observed.wg.device = some (Index.releasedPeerDevice d pid p) at effect
      rw [run] at effect
      obtain ⟨observed, equality, device⟩ := effect
      have observedEq : Campaign2.snapshot final after = observed := by
        exact congrArg Prod.snd (Except.ok.inj equality)
      rw [← observedEq] at device
      change final.dev = some (Index.releasedPeerDevice d pid p) at device
      simpa [workAt, workKernel, device, hd, hp, Index.releasedPeerDevice, last,
        Std.TreeMap.getElem?_insert] using pre.2

theorem handshakeSendWorker_workView (pid : PeerId) (identity attempts refs : Nat)
    (queue : List PeerId) (pending : Bool) (retained : 1 < refs) :
    Ensures (handshakeSendWorker pid)
      (fun g => workerAt g pid = some (identity, attempts, refs) ∧
        workAt g pid = (some queue, some pending))
      (fun _ g => workAt g pid = (some queue, some pending)) := by
  unfold handshakeSendWorker
  refine ensures_bind (Q := fun _ g => workerAt g pid = some (identity, attempts, refs) ∧
    workAt g pid = (some queue, some pending)) _ _ ?_ ?_
  · intro g ambient result final after pre run
    exact ⟨sendHandshakeInitiation_workerView pid (identity, attempts, refs)
      g ambient result final after pre.1 run,
      sendHandshakeInitiation_workView pid queue pending g ambient result final after pre.2 run⟩
  · intro _
    exact retained_peerPut_workView pid identity attempts refs queue pending retained

end Leanux.Proofs.WG.TimerDiscipline
