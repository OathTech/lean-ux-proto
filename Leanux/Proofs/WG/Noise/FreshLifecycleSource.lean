import Leanux.Proofs.WG.Noise.FreshLifecycleFrames
import Leanux.Proofs.WG.Noise.FreshHistoryEffects
import Leanux.Proofs.WG.Noise.CryptoFrames
import Leanux.Proofs.WG.Config.BranchSource
import Leanux.Proofs.WG.Config.ExpiryEffects
import Leanux.Proofs.WG.Noise.ClearSource
import Leanux.Proofs.WG.Roaming.ResponseConsumeSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

/-- Local variant of Keypairs.Frames.WGBase.indexLookup_spec. Normal lookup
preserves the tracked optional next slot and allocation cursor, and supplies its actual held reference;
owner/reference aliasing and failed-owner clears remain. -/
theorem indexLookup_spec_freshTransport_variant (tracked : PeerId) (kinds : List IndexKind) (index : Nat) (entry : Option Device) :
    Ensures (indexLookup kinds index) (FreshTransport tracked entry)
      (fun out g => FreshTransport tracked entry g ∧
        ∀owner pid, out = some (owner,pid) → ∃d p,
          g.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount) := by
  intro g ambient out final after pre run
  cases device : g.dev with
  | none =>
    rw [Index.indexLookup_factor] at run
    simp [Index.lookupPrefix, liftIndex, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases out with
    | none =>
      obtain ⟨next,effect,cause,facts,_⟩ :=
        Index.indexLookup_none kinds index d g ambient none final after device run rfl
      have same : freshInstallView tracked (some next) = freshInstallView tracked (some d) := by
        cases cause with
        | absentOrDisallowed => exact congrArg (fun x => freshInstallView tracked (some x)) facts.2
        | nullOwnerWord =>
          obtain ⟨owner,_,_,_,rfl⟩ := facts
          exact freshInstallView_owner tracked d owner none
        | zeroReference =>
          obtain ⟨owner,_,_,_,_,_,_,_,rfl⟩ := facts
          exact freshInstallView_owner tracked d owner none
      refine ⟨?_, ?_⟩
      · change freshInstallView tracked final.dev = _
        rw [effect, same]; simpa [FreshTransport,device] using pre
      · intro owner pid impossible; cases impossible
    | some pair =>
      obtain ⟨owner,pid⟩ := pair
      obtain ⟨_,_,word,p,resident,positive,_,effect⟩ :=
        Index.indexLookup_success kinds index d g ambient (some (owner,pid)) final after device run owner pid rfl
      have acquiredWord := Index.acquirePeer_word d pid p owner (some pid) resident word
      have unchanged := Index.writeOwnerWord_same_peers (Index.acquirePeer d pid p) owner (some pid) acquiredWord
      refine ⟨?_, ?_⟩
      · change freshInstallView tracked final.dev = _
        rw [effect, freshInstallView_owner]
        have same := freshInstallView_write tracked pid d p {p with refcount := p.refcount + 1} resident rfl
        change freshInstallView tracked (some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}}) = _
        rw [same]; simpa [FreshTransport,device] using pre
      · intro own target returned
        cases returned
        refine ⟨_,{p with refcount := p.refcount + 1},effect,?_,by change 1 < p.refcount + 1; omega⟩
        rw [unchanged]
        simp [Index.acquirePeer]


/-- Whole-call variant of Keypairs.Frames.WGTransitions.createInitiation_spec,
composed from owned native writes, crypto contracts and the actual typed index
adapter. Every early normal refusal retains the cursor/next view. -/
theorem createInitiation_spec_freshTransport_variant (pid tracked : PeerId)
    (entry : Option Device) :
    Ensures (createInitiation pid) (FreshTransport tracked entry)
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

  have hdev : Ensures getDev P (fun _ => P) := by
    intro g ambient x g' ambient' hp hr
    cases hd : g.dev with
    | none => simp [getDev,hd,invariant,AmbientM.invariant] at hr; cases hr
    | some d =>
      simp [getDev,hd] at hr
      rcases hr with ⟨⟨rfl,rfl⟩,rfl⟩
      exact hp
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
      | none => exact hstop _ R
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
          | none => exact hstop _ R
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
              | none => exact hstop _ R
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
                refine ensures_bind _ _ (hcommit HANDSHAKE_CREATED_INITIATION) ?_
                intro _ g ambient x g' ambient' hp hr
                cases hr
                exact hp

/-- Whole-call variant of Keypairs.Frames.WGTransitions.consumeResponse_spec.
The actual lookup supplies the retained cleanup reference; no public budget,
owner-word relation, readiness or successful-prefix premise is imposed. -/
theorem consumeResponse_spec_freshTransport_variant (msg : List UInt8) (tracked : PeerId)
    (entry : Option Device) :
    Ensures (consumeResponse msg) (FreshTransport tracked entry)
      (fun _ => FreshTransport tracked entry) := by
  let safe := FreshTransport tracked entry
  let R : Option Roaming.ResponseConsumed → WGWorld → Prop := fun _ => safe
  change Ensures (consumeResponse msg) safe (fun _ => safe)
  have hstop {α : Type} (P : WGWorld → Prop) (message : String) (Q : α → WGWorld → Prop) :
      Ensures (invariant message : WG.M α) P Q := by
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
  have hnone : Ensures (pure (none : Option Roaming.ResponseConsumed) : WG.M _) safe R := by
    intro g a r final after pre run
    cases run
    exact pre
  have hfail (pid : PeerId) :
      Ensures (do peerPut (some pid); pure (none : Option Roaming.ResponseConsumed))
        (FreshTransportHeld tracked entry pid) R :=
    ensures_bind _ _ (peerPut_freshTransportHeld tracked entry pid) (fun _ => hnone)
  have hcommit (pid : PeerId) (f : Peer → Peer)
      (next : ∀p, (f p).keypairNext = p.keypairNext) :
      Ensures (modifyPeer pid f) (FreshTransportHeld tracked entry pid)
        (fun _ => safe) := by
    intro g ambient result final after pre run
    exact modifyPeer_spec_freshTransport_variant tracked entry pid f next
      g ambient result final after pre.1 run
  have htail (input : Roaming.ResponseInput) :
      Ensures (Roaming.responseConsumeTail msg input) (FreshTransportHeld tracked entry input.pid) R := by
    let P := FreshTransportHeld tracked entry input.pid
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
      | none => exact hstop P _ R
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
          | none => exact hstop P _ R
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
              | none => exact hstop P _ R
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
                    (hcommit input.pid
                      (fun p => {p with remoteEphemeral := (msg.drop 12).take 32, hash := hash, chainingKey := ck, remoteIndex := u32le msg 4, handshakeState := HANDSHAKE_CONSUMED_RESPONSE})
                      (fun _ => rfl)) ?_
                  intro _
                  refine ensures_bind _ _ (hsnapshot safe) ?_
                  intro observed g a r final after pre run
                  cases run
                  exact pre
  have hchecked (identity : StaticIdentity) (owner pid : PeerId) :
      Ensures (do
        let p ← getPeer pid
        if ← branch .crespNotCreatedInitiation (p.handshakeState != HANDSHAKE_CREATED_INITIATION) then
          peerPut (some pid)
          return none
        Roaming.responseConsumeTail msg ⟨identity,owner,pid,p⟩)
        (FreshTransportHeld tracked entry pid) R := by
    refine ensures_bind _ _ (hread _ pid) ?_
    intro p
    refine ensures_bind _ _ (hbranch _ _ _) ?_
    intro wrong
    cases wrong with
    | true => exact hfail pid
    | false => exact htail ⟨identity,owner,pid,p⟩
  have hlookup : Ensures (indexLookup [.handshake] (u32le msg 8)) safe
      (fun result g => safe g ∧ ∀owner pid, result = some (owner,pid) →
        ∃d p, g.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount) :=
    indexLookup_spec_freshTransport_variant tracked [.handshake] (u32le msg 8) entry
  have hconsume : Ensures (Roaming.responseConsume msg) safe R := by
    unfold Roaming.responseConsume
    refine ensures_bind _ _ hdev ?_
    intro d
    refine ensures_bind _ _ (hbranch safe _ _) ?_
    intro absent
    cases absent with
    | true => exact hnone
    | false =>
      refine ensures_bind _ _ hlookup ?_
      intro entry
      refine ensures_bind _ _ (hbranch _ _ _) ?_
      intro missing
      cases missing with
      | true =>
        intro g a r final after pre run
        exact hnone g a r final after pre.1 run
      | false =>
        cases entry with
        | none => exact hstop _ _ R
        | some pair =>
          obtain ⟨owner,pid⟩ := pair
          cases owner with
          | keypair id => exact hstop _ _ R
          | handshake own =>
            intro g a r final after pre run
            exact hchecked d.staticIdentity own pid g a r final after
              ⟨pre.1,pre.2 (.handshake own) pid rfl⟩ run
  rw [← Roaming.responseConsume_erase]
  refine ensures_bind _ _ hconsume ?_
  intro out g ambient result final after pre run
  cases run
  exact pre




/-- Project the already checked exact handshake-clear effect. Normal clearing
preserves every tracked next slot and the allocation cursor; NULL words and
missing peers retain their original Stops. -/
theorem handshakeClear_freshTransport (pid tracked : PeerId) (entry : Option Device) :
    Ensures (handshakeClear pid) (FreshTransport tracked entry)
      (fun _ => FreshTransport tracked entry) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [handshakeClear,IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
      device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [handshakeClear,IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
        device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have exactClear : Ensures (handshakeClear pid) (fun g => g.dev = some d)
          (fun _ g => g.dev = some (Config.expiryZeroDevice d pid p)) := by
        simpa only [Config.expiryReadPrefix,requireNotPending,pure_bind] using
          Config.expiryReadPrefix_exact pid d p resident
      have effect := exactClear g ambient result final after device run
      have same : freshInstallView tracked (some (Config.expiryZeroDevice d pid p)) =
          freshInstallView tracked (some d) := by
        by_cases equal : pid = tracked
        · subst tracked
          simp [freshInstallView,Config.expiryZeroDevice,Config.withPeer,Config.zeroedHandshake,resident]
        · simp [freshInstallView,Config.expiryZeroDevice,Config.withPeer,Std.TreeMap.getElem?_insert,equal]
      change freshInstallView tracked final.dev = _
      rw [effect,same]
      simpa [FreshTransport,device] using pre

/-- Project actual clock/reset and invalidation effects, without record or key
readiness. Expiry invalidates keys but does not clear the peer's slots. -/
theorem expireCurrentPeerKeypairs_freshTransport (pid tracked : PeerId) (entry : Option Device) :
    Ensures (expireCurrentPeerKeypairs pid) (FreshTransport tracked entry)
      (fun _ => FreshTransport tracked entry) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [expireCurrentPeerKeypairs,requireNotPending,handshakeClear,
      IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
      device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [expireCurrentPeerKeypairs,requireNotPending,handshakeClear,
        IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
        device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨now,effect⟩ := Config.expireCurrent_exact pid d p resident
        g ambient result final after device run
      have invalidate (before : Device) (key : Option KeypairId) :
          freshInstallView tracked (some (Config.invalidateDevice before key)) =
          freshInstallView tracked (some before) := by
        cases key with
        | none => rfl
        | some id => cases found : before.keypairs[id]? <;> simp only [Config.invalidateDevice,found] <;> rfl
      have same : freshInstallView tracked (some (Config.expiredDevice d pid p now)) =
          freshInstallView tracked (some d) := by
        simp only [Config.expiredDevice,invalidate]
        by_cases equal : pid = tracked
        · subst tracked
          simp [freshInstallView,Config.expiryHeadDevice,Config.withPeer,Config.zeroedHandshake,resident]
        · simp [freshInstallView,Config.expiryHeadDevice,Config.withPeer,Std.TreeMap.getElem?_insert,equal]
      change freshInstallView tracked final.dev = _
      rw [effect,same]
      simpa [FreshTransport,device] using pre

/-- Ordered actual keypair clearing forgets next without rewinding the cursor.
No static release budget is assumed; aliases and failed puts remain Stops. -/
theorem keypairsClear_freshView (pid : PeerId) (entry : Option Device) :
    Ensures (keypairsClear pid) (FreshTransport pid entry)
      (fun _ final => FreshViewStep (freshInstallView pid entry) none
        (freshInstallView pid final.dev)) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [keypairsClear,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [keypairsClear,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨last,finalDevice,steps⟩ := keypairsClear_effect pid d p resident
        g ambient result final after device run
      have peer := keypairsClear_peer pid p g ambient result final after
        (by simp [peerAt,device,resident]) run
      have cursor := clearRun_allocation_cursor steps
      have finalPeer : last.peers[pid]? = some {p with
          keypairNext := none,keypairPrevious := none,keypairCurrent := none} := by
        simpa [peerAt,finalDevice] using peer
      change freshInstallView pid g.dev = freshInstallView pid entry at pre
      rw [← pre,device,finalDevice]
      simpa [freshInstallView,resident,finalPeer,cursor] using
        FreshViewStep.clearNext d.nextKeypairId p.keypairNext

end Leanux.Proofs.WG.Noise
