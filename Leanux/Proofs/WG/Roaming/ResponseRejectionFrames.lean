import Leanux.Proofs.WG.Roaming.ResponseRejectionModel
import Leanux.Proofs.WG.Index.OwnerCoherenceFrames
import Leanux.Proofs.WG.Index.LookupNoneSource
import Leanux.Proofs.WG.Config.PeerScalars
import Leanux.Proofs.WG.Noise.CryptoFrames
import Leanux.Proofs.WG.Roaming.RateLimitFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

def responseEndpointMap (device : Option Device) (pid : PeerId) : Option (Option Endpoint) :=
  (device.bind fun d => d.peers[pid]?).map Peer.endpoint

def ResponseEndpointHeld (entry : Option Device) (pid : PeerId) (g : WGWorld) : Prop :=
  responseEndpointMap g.dev = responseEndpointMap entry ∧
    ∃d p, g.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount

private theorem endpoint_write (d : Device) (pid : PeerId) (p q : Peer)
    (resident : d.peers[pid]? = some p) (endpoint : q.endpoint = p.endpoint) :
    responseEndpointMap (some {d with peers := d.peers.insert pid q}) = responseEndpointMap (some d) := by
  funext other
  by_cases same : pid = other
  · subst other; simp [responseEndpointMap, resident, endpoint]
  · simp [responseEndpointMap, Std.TreeMap.getElem?_insert, same]

private theorem endpoint_owner (d : Device) (owner : IndexOwner) (word : Option PeerId) :
    responseEndpointMap (some (Index.writeOwnerWord d owner word)) = responseEndpointMap (some d) := by
  cases owner with
  | keypair id => cases found : d.keypairs[id]? <;> simp only [Index.writeOwnerWord, found] <;> rfl
  | handshake pid =>
    cases found : d.peers[pid]? with
    | none => simp [Index.writeOwnerWord, found]
    | some p => simp only [Index.writeOwnerWord, found]; exact endpoint_write d pid p _ found rfl

/-- Normal lookup preserves all optional endpoint observations and supplies its
actual held reference; owner/reference aliasing and failed-owner clears remain. -/
theorem indexLookup_responseEndpoints (kinds : List IndexKind) (index : Nat) (entry : Option Device) :
    Ensures (indexLookup kinds index) (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun out g => responseEndpointMap g.dev = responseEndpointMap entry ∧
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
      have same : responseEndpointMap (some next) = responseEndpointMap (some d) := by
        cases cause with
        | absentOrDisallowed => exact congrArg (fun x => responseEndpointMap (some x)) facts.2
        | nullOwnerWord =>
          obtain ⟨owner,_,_,_,rfl⟩ := facts
          exact endpoint_owner d owner none
        | zeroReference =>
          obtain ⟨owner,_,_,_,_,_,_,_,rfl⟩ := facts
          exact endpoint_owner d owner none
      refine ⟨?_, ?_⟩
      · rw [effect, same]; simpa [device] using pre
      · intro owner pid impossible; cases impossible
    | some pair =>
      obtain ⟨owner,pid⟩ := pair
      obtain ⟨_,_,word,p,resident,positive,_,effect⟩ :=
        Index.indexLookup_success kinds index d g ambient (some (owner,pid)) final after device run owner pid rfl
      have acquiredWord := Index.acquirePeer_word d pid p owner (some pid) resident word
      have unchanged := Index.writeOwnerWord_same_peers (Index.acquirePeer d pid p) owner (some pid) acquiredWord
      refine ⟨?_, ?_⟩
      · rw [effect, endpoint_owner]
        have same := endpoint_write d pid p {p with refcount := p.refcount + 1} resident rfl
        change responseEndpointMap (some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}}) = _
        rw [same]; simpa [device] using pre
      · intro own target returned
        cases returned
        refine ⟨_,{p with refcount := p.refcount + 1},effect,?_,by change 1 < p.refcount + 1; omega⟩
        rw [unchanged]
        simp [Index.acquirePeer]

/-- Rejection releases the actual held reference, so no peer is removed. -/
theorem peerPut_responseEndpoints (entry : Option Device) (pid : PeerId) :
    Ensures (peerPut (some pid)) (ResponseEndpointHeld entry pid)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry) := by
  intro g ambient result final after pre run
  obtain ⟨same,d,p,device,resident,retained⟩ := pre
  have effect := ((ensures_iff _ _ _).mpr (Config.peerPut_retained pid d p resident retained))
    g ambient result final after device run
  rw [effect]
  exact (endpoint_write d pid p {p with refcount := p.refcount-1} resident rfl).trans (by simpa [device] using same)

/-- Every normal response-consumption return preserves all optional endpoints.
Actual lookup supplies the held reference for every rejected-response put;
there is no readiness, residency, reference-budget or successful-result premise. -/
theorem consumeResponse_endpoints (msg : List UInt8) (entry : Option Device) :
    Ensures (consumeResponse msg) (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry) := by
  let safe : WGWorld → Prop := fun g => responseEndpointMap g.dev = responseEndpointMap entry
  change Ensures (consumeResponse msg) safe (fun _ => safe)
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
        (ResponseEndpointHeld entry pid) (fun _ => safe) :=
    ensures_bind _ _ (peerPut_responseEndpoints entry pid) (fun _ => hpure safe none)
  have hmodify (pid : PeerId) (f : Peer → Peer)
      (endpoint : ∀p, (f p).endpoint = p.endpoint)
      (count : ∀p, (f p).refcount = p.refcount) :
      Ensures (modifyPeer pid f) (ResponseEndpointHeld entry pid)
        (fun _ => ResponseEndpointHeld entry pid) := by
    intro g ambient result final after pre run
    obtain ⟨same,d,p,device,resident,retained⟩ := pre
    change (((do let p ← getPeer pid; setPeer pid (f p)) : WG.M Unit).run g).run ambient = _ at run
    simp [getPeer, getDev, device, resident, setPeer, modifyDev] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    refine ⟨?_,_,f p,rfl,by simp,?_⟩
    · exact (endpoint_write d pid p (f p) resident (endpoint p)).trans (by simpa [device] using same)
    · simpa only [count] using retained
  have htail (input : Roaming.ResponseInput) :
      Ensures (Roaming.responseConsumeTail msg input) (ResponseEndpointHeld entry input.pid)
        (fun _ => safe) := by
    let P := ResponseEndpointHeld entry input.pid
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
                    (hmodify input.pid
                      (fun p => {p with remoteEphemeral := (msg.drop 12).take 32, hash := hash, chainingKey := ck, remoteIndex := u32le msg 4, handshakeState := HANDSHAKE_CONSUMED_RESPONSE})
                      (fun _ => rfl) (fun _ => rfl)) ?_
                  intro _
                  refine ensures_bind _ _ (hsnapshot P) ?_
                  intro observed g a r final after pre run
                  cases run
                  exact pre.1
  have hchecked (identity : StaticIdentity) (owner pid : PeerId) :
      Ensures (do
        let p ← getPeer pid
        if ← branch .crespNotCreatedInitiation (p.handshakeState != HANDSHAKE_CREATED_INITIATION) then
          peerPut (some pid)
          return none
        Roaming.responseConsumeTail msg ⟨identity,owner,pid,p⟩)
        (ResponseEndpointHeld entry pid) (fun _ => safe) := by
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
    indexLookup_responseEndpoints [.handshake] (u32le msg 8) entry
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
              ⟨pre.1,pre.2 (.handshake own) pid rfl⟩ run
  rw [← Roaming.responseConsume_erase]
  exact ensures_bind _ _ hconsume (fun out => hpure safe (Roaming.responsePeer out))


/-- Frame the actual response cut only under its own actual MAC admission.
No cookie-reply continuation is treated as a consumer rejection. -/
theorem responseCallPrefix_admitted_endpoints (msg : List UInt8) (src : SkbSource)
    (g : WGWorld) (ambient : Ambient) (loaded : Bool) (mac : MacState)
    (middle : WGWorld) (inputs : Ambient) (result : Option ResponseCallCut)
    (final : WGWorld) (after : Ambient)
    (macRun : ((rateLimitPrefix msg src).run g).run ambient = .ok (((loaded,mac),middle),inputs))
    (admitted : responseMacAdmitted loaded mac)
    (run : ((responseCallPrefix msg src).run g).run ambient = .ok ((result,final),after)) :
    responseEndpointMap final.dev = responseEndpointMap g.dev := by
  have preserved := rateLimitPrefix_peers msg src g g ambient (loaded,mac) middle inputs rfl macRun
  have bindRun {α β : Type} (a : WG.M α) (f : α → WG.M β)
      (g : WGWorld) (ambient : Ambient) :
      (((a >>= f).run g).run ambient) =
        (((a.run g).run ambient) >>= fun ((x,current),middle) => ((f x).run current).run middle) := rfl
  have branchRun (site : Decision) (value : Bool) (g : WGWorld) (ambient : Ambient) :
      (((branch site value : WG.M Bool).run g).run ambient) =
        .ok ((value,g),{ambient with steps := ambient.steps.push {
          decision := site, outcome := value, netRx := ambient.netRxSection}}) := rfl
  have pureRun {α : Type} (x : α) (g : WGWorld) (ambient : Ambient) :
      (((pure x : WG.M α).run g).run ambient) = .ok ((x,g),ambient) := rfl
  have okBind {α β : Type} (x : α) (f : α → Except Stop β) :
      (Except.ok x >>= f) = f x := rfl
  have accepted (loaded : Bool) (mac : MacState) :
      Ensures (do
        let consumed ← responseWithLookup msg
        if ← branch .hsRespNoPeer consumed.isNone then return none
        let some pair := consumed | invariant "unreachable"
        return some ⟨loaded,mac,pair.1,pair.2,← Campaign2.read⟩ : WG.M (Option ResponseCallCut))
        (fun h => responseEndpointMap h.dev = responseEndpointMap middle.dev)
        (fun _ h => responseEndpointMap h.dev = responseEndpointMap middle.dev) := by
    intro h a out finish last pre execution
    rw [bindRun] at execution
    cases consumedRun : ((responseWithLookup msg).run h).run a with
    | error stop => rw [consumedRun] at execution; cases execution
    | ok pair =>
      obtain ⟨⟨consumed,current⟩,next⟩ := pair
      rw [consumedRun] at execution
      have erased : ((consumeResponse msg).run h).run a =
          .ok ((consumed.map fun pair => pair.2.input.pid,current),next) := by
        rw [← responseWithLookup_erase]
        change (((responseWithLookup msg).run h).run a >>= fun ((out,g),a) =>
          Except.ok ((out.map (fun pair => pair.2.input.pid),g),a)) = _
        rw [consumedRun]; rfl
      have endpoints := consumeResponse_endpoints msg middle.dev h a _ current next pre erased
      cases consumed with
      | none =>
        simp only [okBind, bindRun, branchRun, Option.isNone_none, ite_true, pureRun] at execution
        cases execution; exact endpoints
      | some pair =>
        simp only [okBind, bindRun, branchRun, Option.isNone_some, Bool.false_eq_true, ite_false] at execution
        change Except.ok ((some _,current),_) = Except.ok ((out,finish),last) at execution
        cases execution; exact endpoints
  let logged := {ambient with steps := ambient.steps.push {
    decision := .hsCookie, outcome := false, netRx := ambient.netRxSection}}
  change (((responseLoad.run g).run logged) >>= fun ((loaded,current),next) =>
    ((cookieValidatePacket msg src loaded).run current).run next >>= fun ((mac,finish),last) =>
      Except.ok (((loaded,mac),finish),last)) = _ at macRun
  change (((responseLoad.run g).run logged) >>= fun ((loaded,current),next) =>
    ((responsePacketPrefix msg src loaded).run current).run next) = _ at run
  cases loadRun : (responseLoad.run g).run logged with
  | error stop => rw [loadRun] at macRun; cases macRun
  | ok pair =>
    obtain ⟨⟨load,current⟩,next⟩ := pair
    rw [loadRun] at macRun run
    change (((cookieValidatePacket msg src load).run current).run next >>= fun ((value,finish),last) =>
      Except.ok (((load,value),finish),last)) = _ at macRun
    simp only [okBind] at run
    unfold responsePacketPrefix at run
    rw [bindRun] at run
    cases cookieRun : ((cookieValidatePacket msg src load).run current).run next with
    | error stop => rw [cookieRun] at macRun; cases macRun
    | ok pair =>
      obtain ⟨⟨value,finish⟩,last⟩ := pair
      rw [cookieRun] at macRun run
      cases macRun
      have endpoints : responseEndpointMap middle.dev = responseEndpointMap g.dev := by
        funext pid
        have mapped (device : Option Device) : responseEndpointMap device pid =
            ((device.map Device.peers).bind fun ps => ps[pid]?).map Peer.endpoint := by
          cases device <;> rfl
        rw [mapped,mapped,preserved]
      have resultFrame : responseEndpointMap final.dev = responseEndpointMap middle.dev := by
        rcases admitted with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        all_goals simp only [okBind, WG.andM, WG.orM, bindRun, branchRun, pureRun,
          Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at run
        all_goals exact accepted _ _ middle _ result final after rfl run
      exact resultFrame.trans endpoints

end Leanux.Proofs.WG.Roaming
