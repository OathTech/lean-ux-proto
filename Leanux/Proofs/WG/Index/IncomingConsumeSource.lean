import Leanux.Proofs.WG.Index.OwnerCoherenceFrames
import Leanux.Proofs.WG.Noise.SlotFrames
import Leanux.Proofs.WG.Noise.ClearModel
import Leanux.Proofs.WG.Roaming.InitiationConsumeErasureSource
import Leanux.Proofs.WG.Roaming.ResponseConsumeSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- The original consumer's single source traversal, with actual lookup,
grouped field writes and rejection release as its invariant boundaries. -/
theorem consumeInitiation_preserves_held_source (msg : List UInt8)
    (safe : WGWorld → Prop) (Held : PeerId → WGWorld → Prop)
    (forget : ∀ pid g, Held pid g → safe g)
    (lookupSpec : ∀ key, Ensures (pubkeyLookup key) safe
      (fun result g => safe g ∧ ∀ pid, result = some pid → Held pid g))
    (pay : ∀ pid, Ensures (peerPut (some pid)) (Held pid) (fun _ => safe))
    (write : ∀ pid f,
      (∀ p, (f p).handshakeEntryPeer = p.handshakeEntryPeer) →
      (∀ p, (f p).refcount = p.refcount) →
      (∀ p, clearKeys (f p) = clearKeys p) →
      (∀ p, (f p).internalId = p.internalId) →
      (∀ p, (f p).isDead = p.isDead) →
      Ensures (modifyPeer pid f) (Held pid) (fun _ => Held pid)) :
    Ensures (consumeInitiation msg) safe (fun _ => safe) := by
  have hpure {α : Type} (P : WGWorld → Prop) (value : α) :
      Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g a r final after pre run; cases run; exact pre
  have hstop {α : Type} (P : WGWorld → Prop) (message : String) :
      Ensures (invariant message : WG.M α) P (fun _ => safe) := by
    intro g a r final after pre run; cases run
  have hbranch (P : WGWorld → Prop) (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hcmp (P : WGWorld → Prop) (site : Decision) (value : Bool) (lhs rhs : Int) :
      Ensures (branchCmp site value lhs rhs : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branchCmp site value lhs rhs) P)
  have hclock (P : WGWorld → Prop) (site : HiddenSite) :
      Ensures (hiddenClock64 site : WG.M Int64) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hiddenClock64 site) P)
  have hread (P : WGWorld → Prop) (pid : PeerId) :
      Ensures (getPeer pid) P (fun _ => P) := by
    intro g a r final after pre run
    exact (((ensures_iff _ _ _).mpr (getPeer_spec pid P)) g a r final after pre run).1
  have hdev : Ensures getDev safe (fun _ => safe) := by
    intro g a r final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, device] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hsnapshot (P : WGWorld → Prop) : Ensures Campaign2.read P (fun _ => P) := by
    intro g a r final after pre run; cases run; exact pre
  have hephemeral (P : WGWorld → Prop) (e ck hash : List UInt8) :
      Ensures (messageEphemeral true e ck hash) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (messageEphemeral_wg_spec P true e ck hash)
  have hdh (P : WGWorld → Prop) (ck priv pub : List UInt8) :
      Ensures (mixDh true ck priv pub) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (mixDh_wg_spec P true ck priv pub)
  have hprecomputed (P : WGWorld → Prop) (ck precomputed : List UInt8) :
      Ensures (mixPrecomputedDh ck precomputed) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (mixPrecomputedDh_wg_spec P ck precomputed)
  have hdecrypt (P : WGWorld → Prop) (sealed key hash : List UInt8) :
      Ensures (messageDecrypt sealed key hash) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (messageDecrypt_wg_spec P sealed key hash)
  have hfailNone : Ensures (do
      let _ ← Roaming.initiationOut none none
      pure (none : Option Roaming.InitiationConsumed)) safe (fun _ => safe) := by
    intro g a r final after pre run
    simp [Roaming.initiationOut, branch, AmbientM.branch, peerPut] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact pre
  have hfail (pid : PeerId) : Ensures (do
      let _ ← Roaming.initiationOut (some pid) none
      pure (none : Option Roaming.InitiationConsumed)) (Held pid) (fun _ => safe) := by
    refine ensures_bind _ _ ?_ (fun _ => hpure safe none)
    intro g a r final after pre run
    let marked := {a with steps := a.steps.push {
      decision := .consumeFailedPut, outcome := true, netRx := a.netRxSection}}
    change (((peerPut (some pid)).run g).run marked >>= fun ((_,current),last) =>
      Except.ok ((none,current),last)) = _ at run
    cases put : ((peerPut (some pid)).run g).run marked with
    | error stop => rw [put] at run; cases run
    | ok pair =>
      obtain ⟨⟨value,current⟩,last⟩ := pair
      rw [put] at run
      cases run
      exact pay pid g marked value final after pre put
  have hfinish (identity : StaticIdentity) (s : Key) (pid : PeerId)
      (lookup : Roaming.InitiationLookup) (dhPeer : Peer) (beforeDh : Campaign2.Snapshot)
      (ckSs t hashT : List UInt8) :
      Ensures (Roaming.initiationFinish msg identity s pid lookup dhPeer beforeDh ckSs t hashT)
        (Held pid) (fun _ => safe) := by
    let P := Held pid
    have hwrite (f : Peer → Peer)
        (word : ∀p, (f p).handshakeEntryPeer = p.handshakeEntryPeer)
        (count : ∀p, (f p).refcount = p.refcount)
        (slots : ∀p, clearKeys (f p) = clearKeys p)
        (stamp : ∀p, (f p).internalId = p.internalId)
        (dead : ∀p, (f p).isDead = p.isDead) :
        Ensures (modifyPeer pid f) P (fun _ => P) :=
      write pid f word count slots stamp dead
    have hmaybeThen {α : Type} (condition : Bool) (f : Peer → Peer)
        (word : ∀p, (f p).handshakeEntryPeer = p.handshakeEntryPeer)
        (count : ∀p, (f p).refcount = p.refcount)
        (slots : ∀p, clearKeys (f p) = clearKeys p)
        (stamp : ∀p, (f p).internalId = p.internalId)
        (dead : ∀p, (f p).isDead = p.isDead)
        (next : WG.M α) (post : α → WGWorld → Prop) (following : Ensures next P post) :
        Ensures (if condition then do
          let q ← getPeer pid
          setPeer pid (f q)
          next
        else next) P post := by
      cases condition
      · exact following
      · rw [← bind_assoc]
        exact ensures_bind _ _ (hwrite f word count slots stamp dead) (fun _ => following)
    unfold Roaming.initiationFinish
    refine ensures_bind _ _ (hread P pid) ?_
    intro p
    refine ensures_bind _ _ (hsnapshot P) ?_
    intro beforeChecks
    refine ensures_bind _ _ (hclock P _) ?_
    intro now
    have hgate : Ensures (WG.orM
        (branch .consumeReplay (memcmp t p.latestTimestamp != .gt))
        (branchCmp .consumeFlood
          (p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64 > now)
          (p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64).toInt now.toInt))
        P (fun _ => P) := by
      unfold WG.orM
      refine ensures_bind _ _ (hbranch P _ _) ?_
      intro replay
      cases replay
      · exact hcmp P _ _ _ _
      · exact hpure P true
    refine ensures_bind _ _ hgate ?_
    intro rejected
    cases rejected with
    | true => exact hfail pid
    | false =>
      rw [← bind_assoc]
      refine ensures_bind _ _ (hwrite (fun p => {p with remoteEphemeral := (msg.drop 8).take 32})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) ?_
      intro _
      refine ensures_bind _ _ (hbranch P _ _) ?_
      intro newer
      refine hmaybeThen newer (fun p => {p with latestTimestamp := t})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) _ _ ?_
      rw [← bind_assoc]
      refine ensures_bind _ _ (hwrite
        (fun p => {p with hash := hashT, chainingKey := ckSs, remoteIndex := u32le msg 4})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) ?_
      intro _
      refine ensures_bind _ _ (hclock P _) ?_
      intro consumption
      refine ensures_bind _ _ (hread P pid) ?_
      intro current
      refine ensures_bind _ _ (hcmp P _ _ _ _) ?_
      intro later
      refine hmaybeThen later (fun p => {p with lastInitiationConsumption := consumption})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) _ _ ?_
      rw [← bind_assoc]
      refine ensures_bind _ _ (hwrite (fun p => {p with handshakeState := HANDSHAKE_CONSUMED_INITIATION})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) ?_
      intro _
      have hout : Ensures (Roaming.initiationOut (some pid) (some pid)) P (fun _ => P) := by
        intro g a r final after pre run
        exact (Roaming.initiationOut_effect (some pid) (some pid) P
          g a r final after pre run).2 rfl
      refine ensures_bind _ _ hout ?_
      intro _
      refine ensures_bind _ _ (hsnapshot P) ?_
      intro observed g a r final after pre run
      cases run
      exact forget pid g pre
  have hlookup (key : Key) : Ensures (Roaming.initiationLookup key) safe
      (fun result g => safe g ∧ ∀pid, result.result = some pid → Held pid g) := by
    intro g a result final after pre run
    change (((pubkeyLookup key).run g).run a >>= fun ((value,current),last) =>
      Except.ok ((Roaming.InitiationLookup.mk (Campaign2.snapshot g a)
        (Campaign2.observeResult (((pubkeyLookup key).run g).run a)) value
        (Campaign2.snapshot current last),current),last)) = _ at run
    cases lookup : ((pubkeyLookup key).run g).run a with
    | error stop => rw [lookup] at run; cases run
    | ok pair =>
      obtain ⟨⟨value,current⟩,last⟩ := pair
      rw [lookup] at run
      cases run
      exact lookupSpec key g a value final after pre lookup
  have hconsume : Ensures (Roaming.initiationConsume msg) safe (fun _ => safe) := by
    unfold Roaming.initiationConsume
    refine ensures_bind _ _ hdev ?_
    intro d
    refine ensures_bind _ _ (hbranch safe _ _) ?_
    intro noIdentity
    cases noIdentity with
    | true => exact hfailNone
    | false =>
      refine ensures_bind _ _ (hephemeral safe _ _ _) ?_
      rintro ⟨ck,hash⟩
      refine ensures_bind _ _ (hdh safe _ _ _) ?_
      intro es
      refine ensures_bind _ _ (hbranch safe _ _) ?_
      intro failed
      cases failed with
      | true => exact hfailNone
      | false =>
        cases es with
        | none => exact hstop safe _
        | some pair =>
          obtain ⟨ck,key⟩ := pair
          refine ensures_bind _ _ (hdecrypt safe _ _ _) ?_
          intro st
          refine ensures_bind _ _ (hbranch safe _ _) ?_
          intro failed
          cases failed with
          | true => exact hfailNone
          | false =>
            cases st with
            | none => exact hstop safe _
            | some pair =>
              obtain ⟨s,hash⟩ := pair
              refine ensures_bind _ _ (hlookup s) ?_
              intro lookup
              refine ensures_bind _ _ (hbranch _ _ _) ?_
              intro missing
              cases missing with
              | true =>
                intro g a r final after pre run
                exact hfailNone g a r final after pre.1 run
              | false =>
                cases selected : lookup.result with
                | none =>
                  exact hstop _ _
                | some pid =>
                  have htail : Ensures (do
                      let dhPeer ← getPeer pid
                      let beforeDh ← Campaign2.read
                      let ss ← mixPrecomputedDh ck dhPeer.precomputedStaticStatic
                      if ← branch .consumeSsFailed ss.isNone then
                        let _ ← Roaming.initiationOut (some pid) none
                        return none
                      let some (ckSs,key) := ss | invariant "unreachable"
                      let ts ← messageDecrypt ((msg.drop 88).take 28) key hash
                      if ← branch .consumeTimestampFailed ts.isNone then
                        let _ ← Roaming.initiationOut (some pid) none
                        return none
                      let some (t,hashT) := ts | invariant "unreachable"
                      Roaming.initiationFinish msg d.staticIdentity s pid lookup dhPeer beforeDh ckSs t hashT)
                      (Held pid) (fun _ => safe) := by
                    let P := Held pid
                    refine ensures_bind _ _ (hread P pid) ?_
                    intro dhPeer
                    refine ensures_bind _ _ (hsnapshot P) ?_
                    intro beforeDh
                    refine ensures_bind _ _ (hprecomputed P _ _) ?_
                    intro ss
                    refine ensures_bind _ _ (hbranch P _ _) ?_
                    intro failed
                    cases failed with
                    | true => exact hfail pid
                    | false =>
                      cases ss with
                      | none => exact hstop P _
                      | some pair =>
                        obtain ⟨ckSs,key⟩ := pair
                        refine ensures_bind _ _ (hdecrypt P _ _ _) ?_
                        intro ts
                        refine ensures_bind _ _ (hbranch P _ _) ?_
                        intro failed
                        cases failed with
                        | true => exact hfail pid
                        | false =>
                          cases ts with
                          | none => exact hstop P _
                          | some pair =>
                            obtain ⟨t,hashT⟩ := pair
                            exact hfinish d.staticIdentity s pid lookup dhPeer beforeDh ckSs t hashT
                  intro g a r final after pre run
                  exact htail g a r final after (pre.2 pid rfl) run
  rw [← Roaming.initiationConsume_erase]
  exact ensures_bind _ _ hconsume (fun out => hpure safe (Roaming.initiationPeer out))

/-- The response consumer uses its actual masked lookup and source-held
reference; the cryptographic tail is traversed once. -/
theorem consumeResponse_preserves_held_source (msg : List UInt8)
    (safe : WGWorld → Prop) (Held : PeerId → WGWorld → Prop)
    (forget : ∀ pid g, Held pid g → safe g)
    (lookupSpec : ∀ index, Ensures (indexLookup [.handshake] index) safe
      (fun result g => safe g ∧ ∀ owner pid, result = some (owner,pid) → Held pid g))
    (pay : ∀ pid, Ensures (peerPut (some pid)) (Held pid) (fun _ => safe))
    (write : ∀ pid f,
      (∀ p, (f p).handshakeEntryPeer = p.handshakeEntryPeer) →
      (∀ p, (f p).refcount = p.refcount) →
      (∀ p, clearKeys (f p) = clearKeys p) →
      (∀ p, (f p).internalId = p.internalId) →
      (∀ p, (f p).isDead = p.isDead) →
      Ensures (modifyPeer pid f) (Held pid) (fun _ => Held pid)) :
    Ensures (consumeResponse msg) safe (fun _ => safe) := by
  have hpure {α : Type} (P : WGWorld → Prop) (value : α) :
      Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g a r final after pre run; cases run; exact pre
  have hstop {α : Type} (P : WGWorld → Prop) (message : String) :
      Ensures (invariant message : WG.M α) P (fun _ => safe) := by
    intro g a r final after pre run; cases run
  have hbranch (P : WGWorld → Prop) (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hread (P : WGWorld → Prop) (pid : PeerId) :
      Ensures (getPeer pid) P (fun _ => P) := by
    intro g a r final after pre run
    exact (((ensures_iff _ _ _).mpr (getPeer_spec pid P)) g a r final after pre run).1
  have hdev : Ensures getDev safe (fun _ => safe) := by
    intro g a r final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, device] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hsnapshot (P : WGWorld → Prop) : Ensures Campaign2.read P (fun _ => P) := by
    intro g a r final after pre run; cases run; exact pre
  have hfail (pid : PeerId) :
      Ensures (do peerPut (some pid); pure (none : Option Roaming.ResponseConsumed))
        (Held pid) (fun _ => safe) :=
    ensures_bind _ _ (pay pid) (fun _ => hpure safe none)
  have htail (input : Roaming.ResponseInput) :
      Ensures (Roaming.responseConsumeTail msg input) (Held input.pid)
        (fun _ => safe) := by
    let P := Held input.pid
    have hephemeral (copy : Bool) (e ck hash : List UInt8) :
        Ensures (messageEphemeral copy e ck hash) P (fun _ => P) :=
      (ensures_iff _ _ _).mpr (messageEphemeral_wg_spec P copy e ck hash)
    have hdh (key : Bool) (ck priv pub : List UInt8) :
        Ensures (mixDh key ck priv pub) P (fun _ => P) :=
      (ensures_iff _ _ _).mpr (mixDh_wg_spec P key ck priv pub)
    have hkdf (second third : Bool) (ck data : List UInt8) :
        Ensures (kdf second third ck data) P (fun _ => P) :=
      (ensures_iff _ _ _).mpr (kdf_wg_spec P second third ck data)
    have hout (outs : List (List UInt8)) (i : Nat) :
        Ensures (kdfOut outs i) P (fun _ => P) :=
      (ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs i)
    have hdecrypt (sealed key hash : List UInt8) :
        Ensures (messageDecrypt sealed key hash) P (fun _ => P) :=
      (ensures_iff _ _ _).mpr (messageDecrypt_wg_spec P sealed key hash)
    unfold Roaming.responseConsumeTail
    refine ensures_bind _ _ (hephemeral true _ _ _) ?_
    rintro ⟨ck,hash⟩
    refine ensures_bind _ _ (hdh false _ _ _) ?_
    intro ee
    refine ensures_bind _ _ (hbranch P _ _) ?_
    intro failed
    cases failed with
    | true => exact hfail input.pid
    | false =>
      cases ee with
      | none => exact hstop P _
      | some pair =>
        obtain ⟨ck,unused⟩ := pair
        refine ensures_bind _ _ (hdh false _ _ _) ?_
        intro se
        refine ensures_bind _ _ (hbranch P _ _) ?_
        intro failed
        cases failed with
        | true => exact hfail input.pid
        | false =>
          cases se with
          | none => exact hstop P _
          | some pair =>
            obtain ⟨ck,unused⟩ := pair
            refine ensures_bind _ _ (hkdf true true _ _) ?_
            intro outs
            refine ensures_bind _ _ (hout outs 0) ?_
            intro ck
            refine ensures_bind _ _ (hout outs 1) ?_
            intro tempHash
            refine ensures_bind _ _ (hout outs 2) ?_
            intro key
            refine ensures_bind _ _ (hdecrypt _ _ _) ?_
            intro decrypted
            refine ensures_bind _ _ (hbranch P _ _) ?_
            intro failed
            cases failed with
            | true => exact hfail input.pid
            | false =>
              cases decrypted with
              | none => exact hstop P _
              | some pair =>
                obtain ⟨unused,hash⟩ := pair
                refine ensures_bind _ _ (hread P input.pid) ?_
                intro checked
                refine ensures_bind _ _ (hbranch P _ _) ?_
                intro changed
                cases changed with
                | true => exact hfail input.pid
                | false =>
                  rw [← bind_assoc]
                  refine ensures_bind _ _
                    (write input.pid
                      (fun p => {p with remoteEphemeral := (msg.drop 12).take 32, hash := hash, chainingKey := ck, remoteIndex := u32le msg 4, handshakeState := HANDSHAKE_CONSUMED_RESPONSE})
                      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) ?_
                  intro _
                  refine ensures_bind _ _ (hsnapshot P) ?_
                  intro observed g a r final after pre run
                  cases run
                  exact forget input.pid g pre
  have hchecked (identity : StaticIdentity) (owner pid : PeerId) :
      Ensures (do
        let p ← getPeer pid
        if ← branch .crespNotCreatedInitiation (p.handshakeState != HANDSHAKE_CREATED_INITIATION) then
          peerPut (some pid)
          return none
        Roaming.responseConsumeTail msg ⟨identity,owner,pid,p⟩)
        (Held pid) (fun _ => safe) := by
    refine ensures_bind _ _ (hread _ pid) ?_
    intro p
    refine ensures_bind _ _ (hbranch _ _ _) ?_
    intro wrong
    cases wrong with
    | true => exact hfail pid
    | false => exact htail ⟨identity,owner,pid,p⟩
  have hlookup : Ensures (indexLookup [.handshake] (u32le msg 8)) safe
      (fun result g => safe g ∧ ∀owner pid, result = some (owner,pid) →
        Held pid g) :=
    lookupSpec (u32le msg 8)
  have hconsume : Ensures (Roaming.responseConsume msg) safe (fun _ => safe) := by
    unfold Roaming.responseConsume
    refine ensures_bind _ _ hdev ?_
    intro d
    refine ensures_bind _ _ (hbranch safe _ _) ?_
    intro absent
    cases absent with
    | true => exact hpure safe none
    | false =>
      refine ensures_bind _ _ hlookup ?_
      intro entry
      refine ensures_bind _ _ (hbranch _ _ _) ?_
      intro missing
      cases missing with
      | true =>
        intro g a r final after pre run; cases run; exact pre.1
      | false =>
        cases entry with
        | none => exact hstop _ _
        | some pair =>
          obtain ⟨owner,pid⟩ := pair
          cases owner with
          | keypair id => exact hstop _ _
          | handshake own =>
            intro g a r final after pre run
            exact hchecked d.staticIdentity own pid g a r final after
              (pre.2 (.handshake own) pid rfl) run
  rw [← Roaming.responseConsume_erase]
  exact ensures_bind _ _ hconsume (fun out => hpure safe (Roaming.responsePeer out))

/-- Exact resident acquisition is the only device update made by this public-key
lookup. Normal misses preserve the input, and normal success holds one extra
reference independently of any owner-table invariant. -/
theorem pubkeyLookup_preserves_acquire_source (key : Key) (D : Device → Prop)
    (acquire : ∀ d pid p, d.peers[pid]? = some p → D d → D (acquirePeer d pid p)) :
    Ensures (pubkeyLookup key)
      (fun g => ∀ d, g.dev = some d → D d)
      (fun result g => (∀ d, g.dev = some d → D d) ∧
        ∀ pid, result = some pid → ∃ d p,
          g.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [pubkeyLookup, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases found : d.peerHashtable.find? (·.1 == key) with
    | none =>
      simp [pubkeyLookup, getDev, device, found, peerGetMaybeZero,
        branch, AmbientM.branch] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      exact ⟨pre, by intro pid impossible; cases impossible⟩
    | some pair =>
      obtain ⟨tableKey,pid⟩ := pair
      cases resident : d.peers[pid]? with
      | none =>
        simp [pubkeyLookup, getDev, device, found, peerGetMaybeZero,
          requireNotPending, getPeer, resident, branch, AmbientM.branch,
          invariant, AmbientM.invariant] at run
        cases run
      | some p =>
        by_cases zero : p.refcount = 0
        · simp [pubkeyLookup, getDev, device, found, peerGetMaybeZero,
            requireNotPending, getPeer, resident, refcountIncNotZero, zero,
            branch, branchCmp, AmbientM.branch, AmbientM.branchCmp] at run
          rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
          exact ⟨pre, by intro target impossible; cases impossible⟩
        · by_cases overflow : 2147483647 ≤ p.refcount
          · simp [pubkeyLookup, getDev, device, found, peerGetMaybeZero,
              requireNotPending, getPeer, resident, refcountIncNotZero, zero,
              overflow, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
              unsupported, AmbientM.unsupported] at run
            cases run
          · simp [pubkeyLookup, getDev, device, found, peerGetMaybeZero,
              requireNotPending, getPeer, resident, refcountIncNotZero, zero,
              overflow, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
              setPeer, modifyDev] at run
            rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
            have coherent : D (acquirePeer d pid p) :=
              acquire d pid p resident (pre d device)
            have safe : ∀ actual,
                some (acquirePeer d pid p) = some actual → D actual := by
              intro actual same; cases same; exact coherent
            refine ⟨safe, ?_⟩
            intro target same
            cases same
            exact ⟨acquirePeer d pid p, {p with refcount := p.refcount + 1},
              rfl, by simp [acquirePeer], by simp; omega⟩
end Leanux.Proofs.WG.Index
