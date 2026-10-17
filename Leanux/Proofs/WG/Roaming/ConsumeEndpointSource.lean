import Leanux.Proofs.WG.Roaming.ConsumeEndpointFrames
import Leanux.Proofs.WG.Index.RxQueueOwnerFrames
import Leanux.Proofs.WG.Config.KeyReferences

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- Whole original data admission preserves every optional endpoint. Successful
lookup supplies its own held peer; key acquisition supplies any cleanup key
reference. Zero-key, dead-peer, queue-full and ring-full branches are retained. -/
theorem consumeData_endpoints (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (entry : Option Device) :
    Ensures (consumeData msg src ds)
      (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry) := by
  let safe : WGWorld → Prop := fun g => responseEndpointMap g.dev = responseEndpointMap entry
  let held (id : KeypairId) (pid : PeerId) (g : WGWorld) : Prop :=
    safe g ∧ ∃d p k, g.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount ∧
      d.keypairs[id]? = some k ∧ 1 < k.refcount
  change Ensures _ safe (fun _ => safe)
  have hpure {α : Type} (P : WGWorld → Prop) (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g a r final after pre run; cases run; exact pre
  have hbranch (P : WGWorld → Prop) (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hskb {α : Type} (action : SkbM α) : Ensures (liftSkb action) safe (fun _ => safe) := by
    intro g a r final after pre run
    cases device : g.dev with
    | none => simp [liftSkb,getDev,device,invariant,AmbientM.invariant] at run; cases run
    | some d =>
      cases executed : (action.run {txSkbs := d.txSkbs,rxSkbs := d.rxSkbs,nextSkb := d.nextSkb}).run a with
      | error stop => simp [liftSkb,getDev,device,executed] at run; cases run
      | ok pair =>
        obtain ⟨⟨value,store⟩,inputs⟩ := pair
        simp [liftSkb,getDev,modifyDev,device,executed] at run
        rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
        change responseEndpointMap (some d) = responseEndpointMap entry
        simpa only [safe,device] using pre
  have hheldFrame {α : Type} (action : WG.M α)
      (endpoints : Ensures action safe (fun _ => safe))
      (references : ∀ d, Ensures action (Index.referencesAt d) (fun _ => Index.referencesAt d))
      (id : KeypairId) (pid : PeerId) : Ensures action (held id pid) (fun _ => held id pid) := by
    intro g a r final after pre run
    obtain ⟨same,d,p,k,device,resident,peerHeld,key,keyHeld⟩ := pre
    have framed := endpoints g a r final after same run
    have observed := references d g a r final after (by simp [Index.referencesAt,device]) run
    cases ending : final.dev with
    | none => simp [Index.referencesAt,ending] at observed
    | some next =>
      have sameReferences : Index.ownerReferences next = Index.ownerReferences d := by
        simpa [Index.referencesAt,ending] using observed
      have keys : next.keypairs = d.keypairs := congrArg (fun x => x.2.1) sameReferences
      have peers := congrFun (congrArg (fun x => x.2.2) sameReferences) pid
      change next.peers[pid]?.map (fun p => (p.handshakeEntryPeer,p.refcount)) = _ at peers
      cases found : next.peers[pid]? with
      | none => simp [Index.ownerReferences,found,resident] at peers
      | some q =>
        simp only [Index.ownerReferences,found,resident,Option.map_some,Option.some.injEq,Prod.mk.injEq] at peers
        exact ⟨framed,next,q,k,ending,found,by omega,by simpa [keys] using key,keyHeld⟩
  have hputKey (id : KeypairId) (pid : PeerId) :
      Ensures (keypairPut (some id) false) (held id pid) (fun _ => ResponseEndpointHeld entry pid) := by
    intro g a r final after pre run
    obtain ⟨same,d,p,k,device,resident,peerHeld,key,keyHeld⟩ := pre
    obtain ⟨value,ending,tail,actual,effect⟩ := Config.keypairPut_retained id d k key keyHeld g a device
    rw [run] at actual
    cases actual
    refine ⟨?_,Config.withKeypair d id {k with refcount := k.refcount-1},p,effect,resident,peerHeld⟩
    rw [effect]
    change responseEndpointMap (some d) = responseEndpointMap entry
    simpa only [safe,device] using same
  let afterEnqueue (id : KeypairId) (peer : Option PeerId) (skb : SkbId) (ret : Int) : WG.M Unit := do
    if ← branch .dataEpipe (ret == -EPIPE) then enqueuePerPeerRx (pure ()) skb .dead
    if ← WG.orM (branch .dataEnqueueOk (ret == 0)) (branch .dataEnqueueOkEpipe (ret == -EPIPE)) then return
    keypairPut (some id) false
    peerPut peer
    freeRxSkb skb
  let withKey (id : KeypairId) (pid : PeerId) (peer : Option PeerId) : WG.M Unit := do
    if ← branch .dataPeerDead (← getPeer pid).isDead then
      keypairPut (some id) false
      peerPut peer
      return
    let skb ← newRxSkb {peer := pid,keypair := id,bytes := msg,source := src,ds}
    let ret ← enqueuePerDeviceAndPeerRx skb
    afterEnqueue id peer skb ret
  let afterGet (peer : Option PeerId) (kp : Option KeypairId) : WG.M Unit := do
    if ← branch .dataNoKeypair kp.isNone then
      peerPut peer
      return
    let some id := kp | invariant "unreachable"
    let some pid := peer | invariant "a keypair entry without a peer"
    withKey id pid peer
  let acquired (found : Option (IndexOwner × PeerId)) : WG.M Unit := do
    let (keypair,peer) ← match found with
      | none => pure (none,none)
      | some (IndexOwner.keypair kp,pid) => pure (some kp,some pid)
      | some (IndexOwner.handshake _,_) => invariant "a handshake entry under the keypair mask"
    let kp ← match keypair with
      | none => do keypairGetNull; pure none
      | some kp => keypairGet (some kp)
    afterGet peer kp
  have factor : consumeData msg src ds = (do
      let found ← indexLookup [.keypair] (u32le msg 4)
      acquired found) := rfl
  have hafter (id : KeypairId) (pid : PeerId) (skb : SkbId) (ret : Int) :
      Ensures (afterEnqueue id (some pid) skb ret) (held id pid) (fun _ => safe) := by
    have hfinish : Ensures (do
        if ← WG.orM (branch .dataEnqueueOk (ret == 0))
            (branch .dataEnqueueOkEpipe (ret == -EPIPE)) then return
        keypairPut (some id) false
        peerPut (some pid)
        freeRxSkb skb) (held id pid) (fun _ => safe) := by
      have hor : Ensures (WG.orM (branch .dataEnqueueOk (ret == 0))
          (branch .dataEnqueueOkEpipe (ret == -EPIPE))) (held id pid) (fun _ => held id pid) := by
        unfold WG.orM
        refine ensures_bind _ _ (hbranch _ _ _) ?_
        intro ok
        cases ok with
        | false => exact hbranch _ _ _
        | true => exact hpure _ _
      refine ensures_bind _ _ hor ?_
      intro done
      cases done with
      | true => intro g a r final after pre run; cases run; exact pre.1
      | false =>
        refine ensures_bind _ _ (hputKey id pid) ?_
        intro _
        exact ensures_bind _ _ (peerPut_responseEndpoints entry pid) (fun _ => hskb (SkbStore.freeRx skb))
    unfold afterEnqueue
    refine ensures_bind _ _ (hbranch _ _ _) ?_
    intro pipe
    cases pipe with
    | false => exact hfinish
    | true =>
      exact ensures_bind _ _ (hheldFrame _
        (enqueuePerPeerRx_pure_spec_endpoints_variant skb .dead entry)
        (fun d => Index.enqueuePerPeerRx_pure_spec_references_variant skb .dead d) id pid)
        (fun _ => hfinish)
  have hwith (id : KeypairId) (pid : PeerId) :
      Ensures (withKey id pid (some pid)) (held id pid) (fun _ => safe) := by
    have hpeer : Ensures (getPeer pid) (held id pid) (fun _ => held id pid) := by
      intro g a r final after pre run
      exact (((ensures_iff _ _ _).mpr (getPeer_spec pid (held id pid))) g a r final after pre run).1
    simp only [withKey]
    refine ensures_bind _ _ hpeer ?_
    intro p
    refine ensures_bind _ _ (hbranch _ _ _) ?_
    intro dead
    cases dead with
    | true =>
      refine ensures_bind _ _ (hputKey id pid) ?_
      intro _
      exact ensures_bind _ _ (peerPut_responseEndpoints entry pid) (fun _ => hpure safe ())
    | false =>
      refine ensures_bind _ _ (hheldFrame _ (hskb _)
        (fun d => Index.hoare_liftSkb_references_variant _ d) id pid) ?_
      intro skb
      exact ensures_bind _ _ (hheldFrame _ (enqueuePerDeviceAndPeerRx_spec_endpoints_variant skb entry)
        (fun d => Index.enqueuePerDeviceAndPeerRx_spec_references_variant skb d) id pid) (hafter id pid skb)
  have hget (id : KeypairId) (pid : PeerId) :
      Ensures (afterGet (some pid) (some id)) (held id pid) (fun _ => safe) := by
    unfold afterGet
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (Config.branch_state_spec (held id pid) .dataNoKeypair false)) ?_
    intro value g a r final after pre run
    rcases pre with ⟨rfl,pre⟩
    exact hwith id pid g a r final after pre run
  have hnone (pid : PeerId) :
      Ensures (afterGet (some pid) none) (ResponseEndpointHeld entry pid) (fun _ => safe) := by
    unfold afterGet
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (Config.branch_state_spec (ResponseEndpointHeld entry pid) .dataNoKeypair true)) ?_
    intro value g a r final after pre run
    rcases pre with ⟨rfl,pre⟩
    exact (ensures_bind _ _ (peerPut_responseEndpoints entry pid) (fun _ => hpure safe ()))
      g a r final after pre run
  rw [factor]
  refine ensures_bind _ _ (indexLookup_responseEndpoints [.keypair] (u32le msg 4) entry) ?_
  intro found g ambient result final after pre run
  cases found with
  | none =>
    simp [acquired,afterGet,keypairGetNull,peerPut,branch,AmbientM.branch] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact pre.1
  | some pair =>
    obtain ⟨owner,pid⟩ := pair
    cases owner with
    | handshake other => cases run
    | keypair id =>
      obtain ⟨d,p,device,resident,peerHeld⟩ := pre.2 (.keypair id) pid rfl
      simp only [acquired,pure_bind] at run
      cases key : d.keypairs[id]? with
      | none => simp [keypairGet,getKeypair,getDev,device,key,branch,AmbientM.branch,invariant,AmbientM.invariant] at run; cases run
      | some k =>
        have keyGet : Ensures (keypairGet (some id)) (fun g => g.dev = some d)
            (fun output g => (output = none ∧ ResponseEndpointHeld entry pid g) ∨
              (output = some id ∧ held id pid g)) := by
          intro middle inputs out finish tailInputs before actual
          have outcome := Config.keypairGet_present id d k key middle inputs out finish tailInputs before actual
          by_cases zero : k.refcount = 0
          · simp only [zero,ite_true] at outcome
            refine Or.inl ⟨outcome.1,?_,d,p,outcome.2,resident,peerHeld⟩
            rw [outcome.2]
            simpa only [device] using pre.1
          · simp only [zero,ite_false] at outcome
            refine Or.inr ⟨outcome.1,?_,Config.withKeypair d id {k with refcount := k.refcount+1},p,
              {k with refcount := k.refcount+1},outcome.2,resident,peerHeld,?_,by change 1 < k.refcount+1; omega⟩
            · change responseEndpointMap finish.dev = responseEndpointMap entry
              rw [outcome.2]
              change responseEndpointMap (some d) = responseEndpointMap entry
              simpa only [device] using pre.1
            · simp [Config.withKeypair]
        have composed : Ensures (do let kp ← keypairGet (some id); afterGet (some pid) kp)
            (fun g => g.dev = some d) (fun _ => safe) := by
          refine ensures_bind _ _ keyGet ?_
          intro kp middle inputs out finish tailInputs acquiredKey actual
          rcases acquiredKey with ⟨rfl,noneHeld⟩ | ⟨rfl,someHeld⟩
          · exact hnone pid middle inputs out finish tailInputs noneHeld actual
          · exact hget id pid middle inputs out finish tailInputs someHeld actual
        exact composed g ambient result final after device run

end Leanux.Proofs.WG.Roaming
