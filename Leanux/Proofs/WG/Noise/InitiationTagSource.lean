import Leanux.Proofs.WG.Noise.InitiationTagFrames
import Leanux.Proofs.WG.Noise.CryptoFrames
import Leanux.Proofs.WG.Roaming.InitiationConsumeErasureSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

/-- Local variant of Keypairs.Frames.WGBase.pubkeyLookup_spec. The actual
acquisition preserves every optional tag and supplies a retained reference. -/
theorem pubkeyLookup_spec_initiationTagMap_variant (key : Key) (entry : Option Device) :
    Ensures (pubkeyLookup key)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun result g => responseTagMap g.dev = responseTagMap entry ∧
        ∀pid, result = some pid → ResponseTagHeld entry pid g) := by
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
            have same : responseTagMap (some (Index.acquirePeer d pid p)) =
                responseTagMap entry :=
              (tagMap_write d pid p {p with refcount := p.refcount + 1} resident rfl).trans
                (by simpa [device] using pre)
            refine ⟨same, ?_⟩
            intro target equal
            cases equal
            exact ⟨same, Index.acquirePeer d pid p, {p with refcount := p.refcount + 1},
              rfl, by simp [Index.acquirePeer], by change 1 < p.refcount + 1; omega⟩


theorem consumeInitiation_tagMap (msg : List UInt8) (entry : Option Device) :
    Ensures (consumeInitiation msg)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun result g => ∀target, responseTagMap g.dev target =
        if result = some target then some HANDSHAKE_CONSUMED_INITIATION else responseTagMap entry target) := by
  let safe : WGWorld → Prop := fun g => responseTagMap g.dev = responseTagMap entry
  let effect : Option PeerId → WGWorld → Prop := fun result g => ∀target,
    responseTagMap g.dev target =
      if result = some target then some HANDSHAKE_CONSUMED_INITIATION else responseTagMap entry target
  let R : Option Roaming.InitiationConsumed → WGWorld → Prop :=
    fun out => effect (Roaming.initiationPeer out)
  change Ensures (consumeInitiation msg) safe effect
  have hpure {α : Type} (P : WGWorld → Prop) (value : α) :
      Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g a r final after pre run; cases run; exact pre
  have hstop {α : Type} (P : WGWorld → Prop) (message : String) (Q : α → WGWorld → Prop) :
      Ensures (invariant message : WG.M α) P Q := by
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
  have hnone : Ensures (pure (none : Option Roaming.InitiationConsumed) : WG.M _) safe R := by
    intro g a r final after pre run
    cases run
    intro target
    simpa [R,effect,Roaming.initiationPeer] using congrFun pre target
  have hfailNone : Ensures (do
      let _ ← Roaming.initiationOut none none
      pure (none : Option Roaming.InitiationConsumed)) safe R := by
    intro g a r final after pre run
    simp [Roaming.initiationOut, branch, AmbientM.branch, peerPut] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    intro target
    simpa [R,effect,Roaming.initiationPeer] using congrFun pre target
  have hfail (pid : PeerId) : Ensures (do
      let _ ← Roaming.initiationOut (some pid) none
      pure (none : Option Roaming.InitiationConsumed)) (ResponseTagHeld entry pid) R := by
    refine ensures_bind _ _ ?_ (fun _ => hnone)
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
      exact peerPut_spec_responseTagMap_variant entry pid g marked value final after pre put
  have hfinish (identity : StaticIdentity) (s : Key) (pid : PeerId)
      (lookup : Roaming.InitiationLookup) (dhPeer : Peer) (beforeDh : Campaign2.Snapshot)
      (ckSs t hashT : List UInt8) :
      Ensures (Roaming.initiationFinish msg identity s pid lookup dhPeer beforeDh ckSs t hashT)
        (ResponseTagHeld entry pid) R := by
    let P := ResponseTagHeld entry pid
    have hwrite (f : Peer → Peer)
        (tag : ∀p, (f p).handshakeState = p.handshakeState)
        (count : ∀p, (f p).refcount = p.refcount) :
        Ensures (modifyPeer pid f) P (fun _ => P) :=
      modifyPeer_spec_initiationTagMap_variant entry pid f tag count
    have hcommit : Ensures (modifyPeer pid (fun p => {p with handshakeState := HANDSHAKE_CONSUMED_INITIATION}))
        P (fun _ => effect (some pid)) := by
      intro g ambient result final after pre run
      obtain ⟨same,d,p,device,resident,_⟩ := pre
      change (((do let p ← getPeer pid; setPeer pid {p with handshakeState := HANDSHAKE_CONSUMED_INITIATION}) : WG.M Unit).run g).run ambient = _ at run
      simp [getPeer,getDev,device,resident,setPeer,modifyDev] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      intro target
      by_cases equal : pid = target
      · subst target; simp [responseTagMap]
      · have prior := congrFun same target
        simpa [effect,responseTagMap,device,Std.TreeMap.getElem?_insert,equal] using prior
    have hmaybeThen {α : Type} (condition : Bool) (f : Peer → Peer)
        (tag : ∀p, (f p).handshakeState = p.handshakeState)
        (count : ∀p, (f p).refcount = p.refcount)
        (next : WG.M α) (post : α → WGWorld → Prop) (following : Ensures next P post) :
        Ensures (if condition then do
          let q ← getPeer pid
          setPeer pid (f q)
          next
        else next) P post := by
      cases condition
      · exact following
      · rw [← bind_assoc]
        exact ensures_bind _ _ (hwrite f tag count) (fun _ => following)
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
        (fun _ => rfl) (fun _ => rfl)) ?_
      intro _
      refine ensures_bind _ _ (hbranch P _ _) ?_
      intro newer
      refine hmaybeThen newer (fun p => {p with latestTimestamp := t})
        (fun _ => rfl) (fun _ => rfl) _ _ ?_
      rw [← bind_assoc]
      refine ensures_bind _ _ (hwrite
        (fun p => {p with hash := hashT, chainingKey := ckSs, remoteIndex := u32le msg 4})
        (fun _ => rfl) (fun _ => rfl)) ?_
      intro _
      refine ensures_bind _ _ (hclock P _) ?_
      intro consumption
      refine ensures_bind _ _ (hread P pid) ?_
      intro current
      refine ensures_bind _ _ (hcmp P _ _ _ _) ?_
      intro later
      refine hmaybeThen later (fun p => {p with lastInitiationConsumption := consumption})
        (fun _ => rfl) (fun _ => rfl) _ _ ?_
      rw [← bind_assoc]
      refine ensures_bind _ _ hcommit ?_
      intro _
      have hout : Ensures (Roaming.initiationOut (some pid) (some pid))
          (effect (some pid)) (fun _ => effect (some pid)) := by
        intro g a r final after pre run
        exact (Roaming.initiationOut_effect (some pid) (some pid) (effect (some pid))
          g a r final after pre run).2 rfl
      refine ensures_bind _ _ hout ?_
      intro _
      refine ensures_bind _ _ (hsnapshot (effect (some pid))) ?_
      intro observed g a r final after pre run
      cases run
      exact pre
  have hlookup (key : Key) : Ensures (Roaming.initiationLookup key) safe
      (fun result g => safe g ∧ ∀pid, result.result = some pid → ResponseTagHeld entry pid g) := by
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
      exact pubkeyLookup_spec_initiationTagMap_variant key entry g a value final after pre lookup
  have hconsume : Ensures (Roaming.initiationConsume msg) safe R := by
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
        | none => exact hstop safe _ R
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
            | none => exact hstop safe _ R
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
                  exact hstop _ _ R
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
                      (ResponseTagHeld entry pid) R := by
                    let P := ResponseTagHeld entry pid
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
                      | none => exact hstop P _ R
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
                          | none => exact hstop P _ R
                          | some pair =>
                            obtain ⟨t,hashT⟩ := pair
                            exact hfinish d.staticIdentity s pid lookup dhPeer beforeDh ckSs t hashT
                  intro g a r final after pre run
                  exact htail g a r final after (pre.2 pid rfl) run
  rw [← Roaming.initiationConsume_erase]
  refine ensures_bind _ _ hconsume ?_
  intro out g ambient result final after pre run
  cases run
  exact pre

end Leanux.Proofs.WG.Noise
