import Leanux.Proofs.WG.Queues.RxQueueView
import Leanux.WG.RxData
import Leanux.Proofs.Framing.Index

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Successful-endpoint receive-queue frames for complete original helpers.
These are queue facts, not access logs or error-state claims. Peer release may
delete a queue; every remaining entry retains its epoch, identity and contents. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem getPeer_rxQueues (pid : PeerId) : SameView rxQueues (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' hr
  obtain ⟨rfl, rfl, _⟩ := Peers.getPeer_current pid w v p ambient ambient' hr
  rfl

theorem keypairGet_rxQueues (kp : Option KeypairId) : SameView rxQueues (keypairGet kp) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases kp with
  | none =>
    simp [keypairGet, branch, AmbientM.branch] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    rfl
  | some id =>
    cases hd : w.dev with
    | none =>
      simp [keypairGet, getKeypair, getDev, hd, branch, AmbientM.branch,
        invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hk : d.keypairs[id]? with
      | none =>
        simp [keypairGet, getKeypair, getDev, hd, hk, branch, AmbientM.branch,
          invariant, AmbientM.invariant] at hr
        cases hr
      | some key =>
        simp only [keypairGet, getKeypair, getDev, setKeypair, modifyDev,
          branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, refcountIncNotZero,
          unsupported, invariant, AmbientM.unsupported, AmbientM.invariant,
          StateT.run_bind] at hr
        simp [hd, hk] at hr
        split at hr <;> simp_all
        all_goals try split at hr <;> simp_all
        all_goals try split at hr <;> simp_all
        all_goals try split at hr <;> simp_all
        all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        all_goals
          funext i
          simp [rxQueues, hd]

theorem keypairPut_rxQueues (kp : Option KeypairId) (now : Bool) :
    SameView rxQueues (keypairPut kp now) := by
  apply SameView.of_wp
  intro initial
  let Q := fun w => rxQueues w = initial
  have read (id : KeypairId) : Preserves Q (getKeypair id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a key v b hp hr
    cases hd : w.dev with
    | none =>
      simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hk : d.keypairs[id]? with
      | none =>
        simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
        cases hr
      | some k =>
        simp [getKeypair, getDev, hd, hk] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        exact hp
  have keys (f : Device → Std.TreeMap Nat Keypair) :
      Preserves Q (modifyDev fun d => {d with keypairs := f d}) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v b hp hr
    cases hr
    change rxQueues {w with dev := w.dev.map (fun d => {d with keypairs := f d})} = initial
    have he : rxQueues {w with dev := w.dev.map (fun d => {d with keypairs := f d})} = rxQueues w := by
      funext i
      simp [rxQueues, Option.bind_map, Function.comp_def]
    rw [he]
    exact hp
  have unhash (id : KeypairId) :
      Preserves Q (monadLift (indexRemove (.keypair id)) : WG.M Unit) := by
    apply hoare_liftIndex
    intro w d table hp hd
    change rxQueues {w with dev := some {d with indexTable := table}} = initial
    have he : rxQueues {w with dev := some {d with indexTable := table}} = rxQueues w := by
      funext i
      simp [rxQueues, hd]
    rw [he]
    exact hp
  have owner (id : KeypairId) : Preserves Q (IndexOwner.peerDeref (.keypair id)) :=
    indexOwner_peerDeref_preserves _ Q
  have rc (old : Nat) : Preserves Q (refcountDecAndTest old : WG.M Bool) := by
    let finish : WG.M Bool := do
      if ← branch .refcountSubNonpositive (old == 0) then
        unsupported "refcount_warn_saturate (use after free)"
      if ← branch .refcountSubUnderflow (old < 1) then
        unsupported "refcount_warn_saturate (underflow)"
      return false
    have finishP : Preserves Q finish := by
      unfold finish
      apply preserves_bind (hoare_liftAmbient
        (AmbientM.branch .refcountSubNonpositive (old == 0)) Q)
      intro bad
      cases bad with
      | true =>
        apply (hoare_iff_run_ambient _ _ _).mpr
        intro w a x w' a' _ hr
        change Except.error _ = Except.ok _ at hr
        cases hr
      | false =>
        apply preserves_bind (hoare_liftAmbient
          (AmbientM.branch .refcountSubUnderflow (old < 1)) Q)
        intro bad
        cases bad with
        | true =>
          apply (hoare_iff_run_ambient _ _ _).mpr
          intro w a x w' a' _ hr
          change Except.error _ = Except.ok _ at hr
          cases hr
        | false => exact preserves_pure false
    unfold refcountDecAndTest
    apply preserves_bind (hoare_liftAmbient
      (AmbientM.branchCmp .refcountSubPositive (old > 0) old 0) Q)
    intro positive
    cases positive with
    | false => exact finishP
    | true =>
      apply preserves_bind (hoare_liftAmbient
        (AmbientM.branchCmp .refcountSubToZero (old == 1) old 1) Q)
      intro released
      cases released
      · exact finishP
      · exact preserves_pure true
  unfold keypairPut
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .keypairPutNull kp.isNone) Q)
  intro null
  cases null with
  | true => exact preserves_pure ()
  | false =>
    cases kp with
    | none => exact hoare_liftAmbient (AmbientM.invariant "unreachable") Q
    | some id =>
      apply preserves_bind (read id)
      intro key
      let tail : WG.M Unit := do
        setKeypair id {key with refcount := key.refcount - 1}
        if ← branch .keypairKrefPutReleased (← refcountDecAndTest key.refcount) then
          _ ← IndexOwner.peerDeref (.keypair id)
          (indexRemove (.keypair id) : WG.M Unit)
          modifyDev fun d => {d with keypairs := d.keypairs.erase id}
      have tailP : Preserves Q tail := by
        unfold tail
        apply preserves_bind (keys fun d => d.keypairs.insert id
          {key with refcount := key.refcount - 1})
        intro _
        apply preserves_bind (rc key.refcount)
        intro released
        apply preserves_bind (hoare_liftAmbient
          (AmbientM.branch .keypairKrefPutReleased released) Q)
        intro free
        cases free with
        | false => exact preserves_pure ()
        | true =>
          apply preserves_bind (owner id)
          intro _
          apply preserves_bind (unhash id)
          intro _
          exact keys fun d => d.keypairs.erase id
      apply preserves_bind (hoare_liftAmbient
        (AmbientM.branch .keypairPutUnreferenceNow now) Q)
      intro before
      cases before with
      | false => simpa only [tail, Bool.false_eq_true, ite_false, bind_assoc] using tailP
      | true =>
        simp only [bind_assoc]
        apply preserves_bind (owner id)
        intro _
        apply preserves_bind (unhash id)
        intro _
        simpa only [tail, bind_assoc] using tailP

theorem peerGet_rxQueues (pid : PeerId) : SameView rxQueues (peerGet pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hd : w.dev with
  | none =>
    simp [peerGet, requireNotPending, getPeer, getDev, hd,
      invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      simp [peerGet, requireNotPending, getPeer, getDev, hd, hp,
        invariant, AmbientM.invariant] at hr
      cases hr
    | some peer =>
      simp [peerGet, requireNotPending, getPeer, getDev, setPeer, modifyDev,
        hd, hp, refcountInc, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
        unsupported, AmbientM.unsupported] at hr
      split at hr <;> simp_all
      all_goals try split at hr <;> simp_all
      all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      all_goals
        funext i
        simp only [rxQueues, hd, Option.bind_some]
        exact congrFun (rxMap_insert_same d.ifindex d.peers pid peer
          {peer with refcount := peer.refcount + 1} hp rfl rfl) i

theorem peerGetMaybeZero_rxQueues (pid : Option PeerId) :
    SameView rxQueues (peerGetMaybeZero pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases pid with
  | none =>
    simp [peerGetMaybeZero, branch, AmbientM.branch] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    rfl
  | some pid =>
    cases hd : w.dev with
    | none =>
      simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, hd,
        branch, AmbientM.branch, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, hd, hp,
          branch, AmbientM.branch, invariant, AmbientM.invariant] at hr
        cases hr
      | some peer =>
        simp only [peerGetMaybeZero, requireNotPending, getPeer, getDev, setPeer, modifyDev,
          branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, refcountIncNotZero,
          unsupported, invariant, AmbientM.unsupported, AmbientM.invariant,
          StateT.run_bind] at hr
        simp [hd, hp] at hr
        split at hr <;> simp_all
        all_goals try split at hr <;> simp_all
        all_goals try split at hr <;> simp_all
        all_goals try split at hr <;> simp_all
        all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        all_goals first
        | rfl
        | funext i
          simp only [rxQueues, hd, Option.bind_some]
          exact congrFun (rxMap_insert_same d.ifindex d.peers pid peer
            {peer with refcount := peer.refcount + 1} hp rfl rfl) i

theorem peerPut_rxQueues (pid : Option PeerId) : RetainsRx (peerPut pid) := by
  apply ProjectedAction.of_wp
  intro initial
  let Q := fun w => ResidentsRetained initial (rxQueues w)
  have read (pid : PeerId) : Hoare (getPeer pid) Q
      (fun p w => Q w ∧ ∃ d, w.dev = some d ∧ d.peers[pid]? = some p) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' hp hr
    have hc : Hoare ((getPeer pid).run w) (fun b => w = w ∧ b = ambient)
        (fun out b => out.2 = w ∧ b = ambient ∧
          ∃ d, out.2.dev = some d ∧ d.peers[pid]? = some out.1) :=
      Peers.getPeer_spec pid w ambient w
    obtain ⟨hv, _, d, hd, hl⟩ := (hoare_iff_run _ _ _).mp hc
      ambient (p, v) ambient' ⟨rfl, rfl⟩ hr
    dsimp only at hv hd hl
    subst v
    exact ⟨hp, d, hd, hl⟩
  have write (pid : PeerId) (p : Peer) :
      Hoare (setPeer pid {p with refcount := p.refcount - 1})
        (fun w => Q w ∧ ∃ d, w.dev = some d ∧ d.peers[pid]? = some p)
        (fun _ => Q) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hp hr
    cases hr
    obtain ⟨hp, d, hd, hl⟩ := hp
    have he : rxQueues {w with dev := w.dev.map (fun d =>
        {d with peers := d.peers.insert pid {p with refcount := p.refcount - 1}})} = rxQueues w := by
      funext i
      simp only [rxQueues, hd, Option.map_some, Option.bind_some]
      exact congrFun (rxMap_insert_same d.ifindex d.peers pid p
        {p with refcount := p.refcount - 1} hl rfl rfl) i
    unfold Q
    rw [he]
    exact hp
  have unhash (pid : PeerId) :
      Preserves Q (monadLift (indexRemove (.handshake pid)) : WG.M Unit) := by
    apply hoare_liftIndex
    intro w d table hp hd
    have he : rxQueues {w with dev := some {d with indexTable := table}} = rxQueues w := by
      funext i
      simp [rxQueues, hd]
    unfold Q
    rw [he]
    exact hp
  have erase (pid : PeerId) (p : Peer) :
      Preserves Q (modifyDev fun d =>
        {d with txDropped := d.txDropped + p.staged.length, peers := d.peers.erase pid}) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hp hr
    cases hr
    apply rx_retained_trans hp
    cases hd : w.dev with
    | none =>
      unfold rxQueues
      simp only [hd, Option.map_none, Option.bind_none]
      exact rx_retained_refl _
    | some d =>
      unfold rxQueues
      simp only [hd, Option.map_some, Option.bind_some]
      exact rxMap_erase d.ifindex d.peers pid
  have retire (pid : PeerId) : Preserves Q (retirePeerUnits pid) := by
    unfold retirePeerUnits modifyAmbient
    apply preserves_bind (hoare_liftAmbient
      (modify fun a => {a with unitPeers := a.unitPeers.filter fun (e : Nat × Nat × Nat) =>
        !((Worker.all.find? (·.index == e.2.1)).any Worker.perPeer && e.2.2 == pid)} : AmbientM Unit) Q)
    intro _
    exact hoare_modify _ (fun _ h => h)
  have rc (old : Nat) : Preserves Q (refcountDecAndTest old : WG.M Bool) := by
    let finish : WG.M Bool := do
      if ← branch .refcountSubNonpositive (old == 0) then
        unsupported "refcount_warn_saturate (use after free)"
      if ← branch .refcountSubUnderflow (old < 1) then
        unsupported "refcount_warn_saturate (underflow)"
      return false
    have finishP : Preserves Q finish := by
      unfold finish
      apply preserves_bind (hoare_liftAmbient
        (AmbientM.branch .refcountSubNonpositive (old == 0)) Q)
      intro bad
      cases bad with
      | true =>
        apply (hoare_iff_run_ambient _ _ _).mpr
        intro w a x w' a' _ hr
        change Except.error _ = Except.ok _ at hr
        cases hr
      | false =>
        apply preserves_bind (hoare_liftAmbient
          (AmbientM.branch .refcountSubUnderflow (old < 1)) Q)
        intro bad
        cases bad with
        | true =>
          apply (hoare_iff_run_ambient _ _ _).mpr
          intro w a x w' a' _ hr
          change Except.error _ = Except.ok _ at hr
          cases hr
        | false => exact preserves_pure false
    unfold refcountDecAndTest
    apply preserves_bind (hoare_liftAmbient
      (AmbientM.branchCmp .refcountSubPositive (old > 0) old 0) Q)
    intro positive
    cases positive with
    | false => exact finishP
    | true =>
      apply preserves_bind (hoare_liftAmbient
        (AmbientM.branchCmp .refcountSubToZero (old == 1) old 1) Q)
      intro released
      cases released
      · exact finishP
      · exact preserves_pure true
  have main : Preserves Q (peerPut pid) := by
    unfold peerPut
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerPutNull pid.isNone) Q)
    intro null
    cases null with
    | true => exact preserves_pure ()
    | false =>
      cases pid with
      | none => exact hoare_liftAmbient (AmbientM.invariant "unreachable") Q
      | some pid =>
        simp only [requireNotPending, pure_bind]
        apply hoare_bind _ _ (read pid)
        intro p
        apply hoare_bind _ _ (write pid p)
        intro _
        apply preserves_bind (rc p.refcount)
        intro released
        apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerKrefPutReleased released) Q)
        intro free
        cases free with
        | false => exact preserves_pure ()
        | true =>
          apply preserves_bind (unhash pid)
          intro _
          cases hqueue : p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty ||
              p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty with
          | true =>
            simp only [ite_true]
            apply (hoare_iff_run_ambient _ _ _).mpr
            intro w a x v b hp hr
            change Except.error _ = Except.ok _ at hr
            cases hr
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            apply preserves_bind (erase pid p)
            intro _
            cases ht : PeerTimer.all.find? (fun t => p.timerPending t || (p.wheel t).isSome) with
            | none =>
              exact retire pid
            | some timer =>
              apply (hoare_iff_run_ambient _ _ _).mpr
              intro w a x v b hp hr
              change Except.error _ = Except.ok _ at hr
              cases hr
  exact hoare_consequence main
    (fun w hw => by unfold Q; rw [hw]; exact rx_retained_refl _)
    (fun _ _ h => h)

theorem counterValidate_rxQueues (kp : KeypairId) (nonce : Nat) :
    SameView rxQueues (counterValidate kp nonce) := by
  apply SameView.of_wp
  intro initial
  let Q := fun w => rxQueues w = initial
  have read (id : KeypairId) : Preserves Q (getKeypair id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a key v b hp hr
    cases hd : w.dev with
    | none =>
      simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hk : d.keypairs[id]? with
      | none =>
        simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
        cases hr
      | some k =>
        simp [getKeypair, getDev, hd, hk] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        exact hp
  have keys (f : Device → Std.TreeMap Nat Keypair) :
      Preserves Q (modifyDev fun d => {d with keypairs := f d}) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v b hp hr
    cases hr
    change rxQueues {w with dev := w.dev.map (fun d => {d with keypairs := f d})} = initial
    have he : rxQueues {w with dev := w.dev.map (fun d => {d with keypairs := f d})} = rxQueues w := by
      funext i
      simp [rxQueues, Option.bind_map, Function.comp_def]
    rw [he]
    exact hp
  have store (key : Keypair) : Preserves Q (setKeypair kp key) :=
    keys (fun d => d.keypairs.insert kp key)
  unfold counterValidate
  apply preserves_bind (read kp)
  intro key
  apply preserves_bind
  · unfold WG.orM
    apply preserves_bind (hoare_liftAmbient
      (AmbientM.branchCmp .ctrRejectCounter
        (key.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES + 1)
        key.receivingCounter.counter (REJECT_AFTER_MESSAGES + 1)) Q)
    intro rejected
    cases rejected
    · exact hoare_liftAmbient
        (AmbientM.branchCmp .ctrRejectTheirs (nonce ≥ REJECT_AFTER_MESSAGES)
          nonce REJECT_AFTER_MESSAGES) Q
    · exact preserves_pure true
  · intro rejected
    cases rejected with
    | true => exact preserves_pure false
    | false =>
      apply preserves_bind (hoare_liftAmbient
        (AmbientM.branch .ctrTooOld (COUNTER_WINDOW_SIZE + (nonce + 1) < key.receivingCounter.counter)) Q)
      intro old
      cases old with
      | true => exact preserves_pure false
      | false =>
        apply preserves_bind (hoare_liftAmbient
          (AmbientM.branch .ctrAdvance (nonce + 1 > key.receivingCounter.counter)) Q)
        intro advance
        cases advance with
        | false =>
          dsimp only
          simp only [Bool.false_eq_true, ite_false]
          split
          · apply preserves_bind (store _)
            intro _
            exact preserves_pure _
          · exact hoare_liftAmbient (AmbientM.invariant _) Q
        | true =>
          dsimp only
          simp only [ite_true]
          apply preserves_bind
          · simp only [Std.Legacy.Range.forIn_eq_forIn_range']
            apply list_view_spec rxQueues (fun t => t = initial)
            intro i backtrack
            apply preserves_bind (hoare_liftAmbient (AmbientM.branch .ctrClearIter true) Q)
            intro _
            split
            · apply (hoare_iff_run_ambient _ _ _).mpr
              intro w a x v b hp hr
              change Except.error _ = Except.ok _ at hr
              cases hr
            · exact preserves_pure _
          · intro backtrack
            apply preserves_bind (hoare_liftAmbient (AmbientM.branch .ctrClearIter false) Q)
            intro _
            split
            · apply preserves_bind (store _)
              intro _
              exact preserves_pure _
            · exact hoare_liftAmbient (AmbientM.invariant _) Q

theorem receivedWithKeypair_rxQueues (pid : PeerId) (kp : KeypairId) :
    SameView rxQueues (receivedWithKeypair pid kp) := by
  have firstWrite : SameView rxQueues
      ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
        (fun p => {p with keypairPrevious := p.keypairCurrent})) :=
    modifyPeer_rxQueues pid _ (fun _ => rfl) (fun _ => rfl)
  have secondWrite : SameView rxQueues
      ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
        (fun p => {p with keypairCurrent := some kp, keypairNext := none})) :=
    modifyPeer_rxQueues pid _ (fun _ => rfl) (fun _ => rfl)
  have ambient {α : Type} (a : AmbientM α) :
      SameView rxQueues (StateT.lift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => rxQueues w = initial)
  unfold receivedWithKeypair
  apply SameView.bind (getPeer_rxQueues pid)
  intro p
  apply SameView.bind (ambient (AmbientM.branch .receivedNotNew (p.keypairNext != some kp)))
  intro notNew
  cases notNew with
  | true => exact SameView.pure _ false
  | false =>
    apply SameView.bind (getPeer_rxQueues pid)
    intro q
    apply SameView.bind (ambient (AmbientM.branch .receivedChanged (q.keypairNext != some kp)))
    intro changed
    cases changed with
    | true => exact SameView.pure _ false
    | false =>
      apply SameView.bind (getPeer_rxQueues pid)
      intro saved
      apply SameView.bind firstWrite
      intro _
      apply SameView.bind (keypairPut_rxQueues saved.keypairPrevious true)
      intro _
      apply SameView.bind secondWrite
      intro _
      exact SameView.pure _ true

end Leanux.Proofs.WG.Queues
