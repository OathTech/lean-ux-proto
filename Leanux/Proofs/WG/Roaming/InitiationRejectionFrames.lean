import Leanux.Proofs.WG.Roaming.InitiationRejectionModel
import Leanux.Proofs.WG.Roaming.ResponseRejectionFrames
import Leanux.Proofs.WG.Roaming.InitiationConsumeErasureSource
import Leanux.Proofs.WG.Roaming.InitiationCallSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

private theorem endpoint_write_init (d : Device) (pid : PeerId) (p q : Peer)
    (resident : d.peers[pid]? = some p) (endpoint : q.endpoint = p.endpoint) :
    responseEndpointMap (some {d with peers := d.peers.insert pid q}) = responseEndpointMap (some d) := by
  funext other
  by_cases same : pid = other
  · subst other; simp [responseEndpointMap, resident, endpoint]
  · simp [responseEndpointMap, Std.TreeMap.getElem?_insert, same]


/-- Public-key lookup preserves endpoints and derives the actual retained reference. -/
theorem pubkeyLookup_initiationEndpoints (key : Key) (entry : Option Device) :
    Ensures (pubkeyLookup key)
      (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun result g => responseEndpointMap g.dev = responseEndpointMap entry ∧
        ∀pid, result = some pid → ResponseEndpointHeld entry pid g) := by
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
            have same : responseEndpointMap (some (Index.acquirePeer d pid p)) =
                responseEndpointMap entry :=
              (endpoint_write_init d pid p {p with refcount := p.refcount + 1} resident rfl).trans
                (by simpa [device] using pre)
            refine ⟨same, ?_⟩
            intro target equal
            cases equal
            exact ⟨same, Index.acquirePeer d pid p, {p with refcount := p.refcount + 1},
              rfl, by simp [Index.acquirePeer], by change 1 < p.refcount + 1; omega⟩

/-- Every normal initiation-consumption return preserves endpoints, including rejection cleanup and replay/flood branches. -/
theorem consumeInitiation_endpoints (msg : List UInt8) (entry : Option Device) :
    Ensures (consumeInitiation msg)
      (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry) := by
  let safe : WGWorld → Prop := fun g => responseEndpointMap g.dev = responseEndpointMap entry
  change Ensures (consumeInitiation msg) safe (fun _ => safe)
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
      pure (none : Option Roaming.InitiationConsumed)) (ResponseEndpointHeld entry pid) (fun _ => safe) := by
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
      exact peerPut_responseEndpoints entry pid g marked value final after pre put
  have hfinish (identity : StaticIdentity) (s : Key) (pid : PeerId)
      (lookup : Roaming.InitiationLookup) (dhPeer : Peer) (beforeDh : Campaign2.Snapshot)
      (ckSs t hashT : List UInt8) :
      Ensures (Roaming.initiationFinish msg identity s pid lookup dhPeer beforeDh ckSs t hashT)
        (ResponseEndpointHeld entry pid) (fun _ => safe) := by
    let P := ResponseEndpointHeld entry pid
    have hwrite (f : Peer → Peer)
        (endpoint : ∀p, (f p).endpoint = p.endpoint)
        (count : ∀p, (f p).refcount = p.refcount) :
        Ensures (modifyPeer pid f) P (fun _ => P) := by
      intro g ambient result final after pre run
      obtain ⟨same,d,p,device,resident,retained⟩ := pre
      change (((do let p ← getPeer pid; setPeer pid (f p)) : WG.M Unit).run g).run ambient = _ at run
      simp [getPeer, getDev, device, resident, setPeer, modifyDev] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      refine ⟨?_,_,f p,rfl,by simp,?_⟩
      · exact (endpoint_write_init d pid p (f p) resident (endpoint p)).trans (by simpa [device] using same)
      · simpa only [count] using retained
    have hmaybeThen {α : Type} (condition : Bool) (f : Peer → Peer)
        (endpoint : ∀p, (f p).endpoint = p.endpoint)
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
        exact ensures_bind _ _ (hwrite f endpoint count) (fun _ => following)
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
      refine ensures_bind _ _ (hwrite (fun p => {p with handshakeState := HANDSHAKE_CONSUMED_INITIATION})
        (fun _ => rfl) (fun _ => rfl)) ?_
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
      exact pre.1
  have hlookup (key : Key) : Ensures (Roaming.initiationLookup key) safe
      (fun result g => safe g ∧ ∀pid, result.result = some pid → ResponseEndpointHeld entry pid g) := by
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
      exact pubkeyLookup_initiationEndpoints key entry g a value final after pre lookup
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
                      (ResponseEndpointHeld entry pid) (fun _ => safe) := by
                    let P := ResponseEndpointHeld entry pid
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

/-- Actual MAC admission excludes the cookie-reply path; the complete initiation prefix then preserves endpoints. -/
theorem initiationCallPrefix_admitted_endpoints (msg : List UInt8) (src : SkbSource)
    (g : WGWorld) (ambient : Ambient) (loaded : Bool) (mac : MacState)
    (middle : WGWorld) (inputs : Ambient) (result : Option InitiationCallCut)
    (final : WGWorld) (after : Ambient)
    (macRun : ((rateLimitPrefix msg src).run g).run ambient = .ok (((loaded,mac),middle),inputs))
    (admitted : initiationMacAdmitted loaded mac)
    (run : ((initiationCallPrefix msg src).run g).run ambient = .ok ((result,final),after)) :
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
        let consumed ← initiationConsume msg
        if ← branch .hsInitNoPeer consumed.isNone then return none
        let some pair := consumed | invariant "unreachable"
        return some ⟨loaded,mac,pair,← Campaign2.read⟩ : WG.M (Option InitiationCallCut))
        (fun h => responseEndpointMap h.dev = responseEndpointMap middle.dev)
        (fun _ h => responseEndpointMap h.dev = responseEndpointMap middle.dev) := by
    intro h a out finish last pre execution
    rw [bindRun] at execution
    cases consumedRun : ((initiationConsume msg).run h).run a with
    | error stop => rw [consumedRun] at execution; cases execution
    | ok pair =>
      obtain ⟨⟨consumed,current⟩,next⟩ := pair
      rw [consumedRun] at execution
      have erased : ((consumeInitiation msg).run h).run a =
          .ok ((initiationPeer consumed,current),next) := by
        rw [← initiationConsume_erase]
        change (((initiationConsume msg).run h).run a >>= fun ((out,g),a) =>
          Except.ok ((initiationPeer out,g),a)) = _
        rw [consumedRun]; rfl
      have endpoints := consumeInitiation_endpoints msg middle.dev h a _ current next pre erased
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
    ((initiationPacketPrefix msg src loaded).run current).run next) = _ at run
  cases loadRun : (responseLoad.run g).run logged with
  | error stop => rw [loadRun] at macRun; cases macRun
  | ok pair =>
    obtain ⟨⟨load,current⟩,next⟩ := pair
    rw [loadRun] at macRun run
    change (((cookieValidatePacket msg src load).run current).run next >>= fun ((value,finish),last) =>
      Except.ok (((load,value),finish),last)) = _ at macRun
    simp only [okBind] at run
    unfold initiationPacketPrefix at run
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
