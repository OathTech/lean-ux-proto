import Leanux.Proofs.WG.Noise.FreshInstallFrames
import Leanux.Proofs.WG.Noise.CryptoFrames
import Leanux.Proofs.WG.Config.BranchSource
import Leanux.Proofs.WG.Roaming.InitiationConsumeErasureSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

/-- Variant of Keypairs.Frames.WGTransitions.consumeInitiation_spec. Actual
initiation consumption preserves the exact tracked next slot and allocation
cursor on every normal return, including all rejected prefixes. -/
theorem consumeInitiation_spec_freshTransport_variant (msg : List UInt8)
    (tracked : PeerId) (entry : Option Device) :
    Ensures (consumeInitiation msg) (FreshTransport tracked entry)
      (fun _ => FreshTransport tracked entry) := by
  let safe := FreshTransport tracked entry
  let effect : Option PeerId → WGWorld → Prop := fun _ => safe
  let R : Option Roaming.InitiationConsumed → WGWorld → Prop := fun _ => safe
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
    exact pre
  have hfailNone : Ensures (do
      let _ ← Roaming.initiationOut none none
      pure (none : Option Roaming.InitiationConsumed)) safe R := by
    intro g a r final after pre run
    simp [Roaming.initiationOut, branch, AmbientM.branch, peerPut] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact pre
  have hfail (pid : PeerId) : Ensures (do
      let _ ← Roaming.initiationOut (some pid) none
      pure (none : Option Roaming.InitiationConsumed)) (FreshTransportHeld tracked entry pid) R := by
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
      exact peerPut_freshTransportHeld tracked entry pid g marked value final after pre put
  have hfinish (identity : StaticIdentity) (s : Key) (pid : PeerId)
      (lookup : Roaming.InitiationLookup) (dhPeer : Peer) (beforeDh : Campaign2.Snapshot)
      (ckSs t hashT : List UInt8) :
      Ensures (Roaming.initiationFinish msg identity s pid lookup dhPeer beforeDh ckSs t hashT)
        (FreshTransportHeld tracked entry pid) R := by
    let P := FreshTransportHeld tracked entry pid
    have hwrite (f : Peer → Peer)
        (tag : ∀p, (f p).keypairNext = p.keypairNext)
        (count : ∀p, (f p).refcount = p.refcount) :
        Ensures (modifyPeer pid f) P (fun _ => P) :=
      modifyPeer_freshTransportHeld tracked entry pid f tag count
    have hcommit : Ensures (modifyPeer pid (fun p => {p with handshakeState := HANDSHAKE_CONSUMED_INITIATION}))
        P (fun _ => effect (some pid)) := by
      intro g ambient result final after pre run
      exact (modifyPeer_freshTransportHeld tracked entry pid
        (fun p => {p with handshakeState := HANDSHAKE_CONSUMED_INITIATION})
        (fun _ => rfl) (fun _ => rfl) g ambient result final after pre run).1
    have hmaybeThen {α : Type} (condition : Bool) (f : Peer → Peer)
        (tag : ∀p, (f p).keypairNext = p.keypairNext)
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
      (fun result g => safe g ∧ ∀pid, result.result = some pid → FreshTransportHeld tracked entry pid g) := by
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
      exact pubkeyLookup_spec_freshTransport_variant tracked entry key g a value final after pre lookup
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
                      (FreshTransportHeld tracked entry pid) R := by
                    let P := FreshTransportHeld tracked entry pid
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

/-- Variant of Keypairs.Frames.WGTransitions.createResponse_spec. Actual response
creation preserves the exact tracked next slot and allocation cursor through
every refusal and successful index insertion. -/
theorem createResponse_spec_freshTransport_variant (pid tracked : PeerId)
    (entry : Option Device) :
    Ensures (createResponse pid) (FreshTransport tracked entry)
      (fun _ => FreshTransport tracked entry) := by
  let P := FreshTransport tracked entry
  let R : Option (List UInt8) → WGWorld → Prop := fun _ => P
  change Ensures _ P R
  have hpure : Ensures (pure none : WG.M (Option (List UInt8))) P R := by
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
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hhidden (site : HiddenSite) :
      Ensures (hidden site : WG.M (List UInt8)) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hidden site) P)
  have hwrite (f : Peer → Peer)
      (same : ∀ p, (f p).keypairNext = p.keypairNext) :
      Ensures (do setPeer pid (f (← getPeer pid))) P (fun _ => P) :=
    modifyPeer_spec_freshTransport_variant tracked entry pid f same
  have hcommit (tag : Nat) :
      Ensures (modifyPeer pid (fun p => {p with handshakeState := tag})) P (fun _ => P) :=
    hwrite _ (fun _ => rfl)
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
  have hindex : Ensures (liftIndex (indexInsert (.handshake pid))) P (fun _ => P) := by
    refine (ensures_iff _ _ _).mpr (hoare_liftIndex_variant _ P ?_)
    intro g d table hp hd
    simpa [P,FreshTransport,freshInstallView,hd] using hp

  have hbranchFirst (site : Decision) (value : Bool)
      (f : Bool → WG.M (Option (List UInt8))) (hf : Ensures (f value) P R) :
      Ensures ((branch site value : WG.M Bool) >>= f) P R := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (Leanux.Proofs.WG.Config.branch_state_spec P site value)) ?_
    intro b g ambient x g' ambient' hp hr
    rcases hp with ⟨rfl, hp⟩
    exact hf g ambient x g' ambient' hp hr
  unfold createResponse
  refine ensures_bind _ _ hread ?_
  intro p
  refine hbranchFirst _ _ _ ?_
  by_cases consumed : p.handshakeState = HANDSHAKE_CONSUMED_INITIATION
  · simp only [consumed, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
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
      | none => exact hstop _ R
      | some e =>
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (messageEphemeral_wg_spec P _ _ _ _)) ?_
        intro ephemeral
        rcases ephemeral with ⟨ck, hash⟩
        refine ensures_bind _ _ (hchain _ _) ?_
        intro _
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (mixDh_wg_spec P _ _ _ _)) ?_
        intro ee
        refine ensures_bind _ _ (hbranch _ _) ?_
        intro eeFailed
        cases eeFailed with
        | true => exact hpure
        | false =>
          cases ee with
          | none => exact hstop _ R
          | some ee =>
            rcases ee with ⟨ck, key⟩
            refine ensures_bind _ _ (hchain _ _) ?_
            intro _
            refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (mixDh_wg_spec P _ _ _ _)) ?_
            intro se
            refine ensures_bind _ _ (hbranch _ _) ?_
            intro seFailed
            cases seFailed with
            | true => exact hpure
            | false =>
              cases se with
              | none => exact hstop _ R
              | some se =>
                rcases se with ⟨ck, key⟩
                refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (kdf_wg_spec P _ _ _ _)) ?_
                intro outs
                refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs 0)) ?_
                intro ck
                refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs 1)) ?_
                intro tempHash
                refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs 2)) ?_
                intro key
                refine ensures_bind _ _ (hchain _ _) ?_
                intro _
                refine ensures_bind _ _ hderef ?_
                intro _
                refine ensures_bind _ _ hindex ?_
                intro index
                rw [← bind_assoc]
                refine ensures_bind _ _ (hcommit HANDSHAKE_CREATED_RESPONSE) ?_
                intro _ g ambient x g' ambient' hp hr
                cases hr
                exact hp
  · simp only [bne, beq_eq_false_iff_ne.mpr consumed, Bool.not_false, ↓reduceIte]
    exact hpure


end Leanux.Proofs.WG.Noise
