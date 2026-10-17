import Leanux.Proofs.WG.Index.OwnerReferenceFrames
import Leanux.Proofs.WG.Index.RxQueueOwnerFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceLookupHeldClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceReleaseClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceKeypairReleaseClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Actual normal data ingress preserves resident hashed-owner coherence. The
lookup and key acquisition supply the held references used by cleanup; the
entry contract adds no reference bound, readiness or alias restriction. -/
theorem consumeData_owner_coherent (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Campaign2.Ensures (consumeData msg src ds) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) := by
  let safe : WGWorld → Prop := fun g => ∀ d, g.dev = some d → HashedOwnersCoherent d
  let held (id : KeypairId) (pid : PeerId) (g : WGWorld) : Prop :=
    ∃ d p k, g.dev = some d ∧ HashedOwnersCoherent d ∧
      d.peers[pid]? = some p ∧ 1 < p.refcount ∧ d.keypairs[id]? = some k ∧ 1 < k.refcount
  change Ensures (consumeData msg src ds) safe (fun _ => safe)
  have held_safe (id : KeypairId) (pid : PeerId) (g : WGWorld) (h : held id pid g) : safe g := by
    obtain ⟨d,p,k,device,coherent,_,_,_,_⟩ := h
    intro actual present
    rw [device] at present
    cases present
    exact coherent
  have hpure {α : Type} (P : WGWorld → Prop) (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g a r final after pre run; cases run; exact pre
  have hbranch (P : WGWorld → Prop) (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hheldFrame {α : Type} (action : WG.M α)
      (framed : ∀ d, Ensures action (referencesAt d) (fun _ => referencesAt d))
      (id : KeypairId) (pid : PeerId) : Ensures action (held id pid) (fun _ => held id pid) := by
    intro g ambient result final after pre run
    obtain ⟨d,p,k,device,coherent,peer,peerHeld,key,keyHeld⟩ := pre
    have observed := framed d g ambient result final after (by simp [referencesAt, device]) run
    cases ending : final.dev with
    | none => simp [referencesAt, ending] at observed
    | some next =>
      have same : ownerReferences next = ownerReferences d := by simpa [referencesAt, ending] using observed
      have keys : next.keypairs = d.keypairs := congrArg (fun x => x.2.1) same
      have peers := congrFun (congrArg (fun x => x.2.2) same) pid
      change next.peers[pid]?.map (fun p => (p.handshakeEntryPeer,p.refcount)) = _ at peers
      cases resident : next.peers[pid]? with
      | none => simp [ownerReferences, resident, peer] at peers
      | some q =>
        simp only [ownerReferences, resident, peer, Option.map_some, Option.some.injEq, Prod.mk.injEq] at peers
        exact ⟨next,q,k,ending,ownerReferences_coherent d next same coherent,
          resident,by omega,by simpa [keys] using key,keyHeld⟩
  have hsafeSkb {α : Type} (action : SkbM α) : Ensures (liftSkb action) safe (fun _ => safe) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [liftSkb, getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      have observed := hoare_liftSkb_references_variant action d g ambient result final after
        (by simp [referencesAt, device]) run
      intro next ending
      have same : ownerReferences next = ownerReferences d := by simpa [referencesAt, ending] using observed
      exact ownerReferences_coherent d next same (pre d device)
  have hputPeer (pid : PeerId) :
      Ensures (peerPut (some pid))
        (fun g => safe g ∧ ∃d p, g.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount)
        (fun _ => safe) := by
    intro g ambient result final after pre run
    obtain ⟨before,d,p,device,resident,retained⟩ := pre
    exact peerPut_owner_coherent pid d p resident (by omega)
      (by intro equal; omega) g ambient result final after ⟨device,before⟩ run
  have hputKey (id : KeypairId) (pid : PeerId) :
      Ensures (keypairPut (some id) false) (held id pid)
        (fun _ g => safe g ∧ ∃d p, g.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount) := by
    intro g ambient result final after pre run
    obtain ⟨d,p,k,device,coherent,resident,peerHeld,key,keyHeld⟩ := pre
    have before : safe g := by
      intro actual present; rw [device] at present; cases present; exact coherent
    have afterSafe := keypairPut_owner_coherent (some id) false g ambient result final after before run
    obtain ⟨value,ending,tail,actual,effect⟩ := Config.keypairPut_retained id d k key keyHeld g ambient device
    rw [run] at actual
    cases actual
    refine ⟨afterSafe,Config.withKeypair d id {k with refcount := k.refcount - 1},p,effect,?_,peerHeld⟩
    exact resident
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
    let skb ← newRxSkb {peer := pid, keypair := id, bytes := msg, source := src, ds}
    let ret ← enqueuePerDeviceAndPeerRx skb
    afterEnqueue id peer skb ret
  let afterGet (peer : Option PeerId) (kp : Option KeypairId) : WG.M Unit := do
    if ← branch .dataNoKeypair kp.isNone then
      peerPut peer
      return
    let some id := kp | invariant "unreachable"
    let some pid := peer | invariant "a keypair entry without a peer"
    withKey id pid peer
  let acquired (entry : Option (IndexOwner × PeerId)) : WG.M Unit := do
    let (keypair, peer) ← match entry with
      | none => pure (none, none)
      | some (IndexOwner.keypair kp, pid) => pure (some kp, some pid)
      | some (IndexOwner.handshake _, _) => invariant "a handshake entry under the keypair mask"
    let kp ← match keypair with
      | none => do keypairGetNull; pure none
      | some kp => keypairGet (some kp)
    afterGet peer kp
  have factor : consumeData msg src ds = (do
      let entry ← indexLookup [.keypair] (u32le msg 4)
      acquired entry) := by rfl
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
      | true =>
        intro g a r final after pre run; cases run; exact held_safe id pid g pre
      | false =>
        refine ensures_bind _ _ (hputKey id pid) ?_
        intro _
        exact ensures_bind _ _ (hputPeer pid) (fun _ => hsafeSkb (SkbStore.freeRx skb))
    unfold afterEnqueue
    refine ensures_bind _ _ (hbranch _ _ _) ?_
    intro pipe
    cases pipe with
    | false => exact hfinish
    | true =>
      exact ensures_bind _ _
        (hheldFrame _ (fun d => enqueuePerPeerRx_pure_spec_references_variant skb .dead d) id pid)
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
      exact ensures_bind _ _ (hputPeer pid) (fun _ => hpure safe ())
    | false =>
      refine ensures_bind _ _ (hheldFrame _ (fun d => hoare_liftSkb_references_variant _ d) id pid) ?_
      intro skb
      exact ensures_bind _ _
        (hheldFrame _ (fun d => enqueuePerDeviceAndPeerRx_spec_references_variant skb d) id pid)
        (hafter id pid skb)
  have hget (id : KeypairId) (pid : PeerId) :
      Ensures (afterGet (some pid) (some id)) (held id pid) (fun _ => safe) := by
    unfold afterGet
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (Config.branch_state_spec (held id pid) .dataNoKeypair false)) ?_
    intro value g ambient result final after pre run
    rcases pre with ⟨rfl,pre⟩
    exact hwith id pid g ambient result final after pre run
  have hlookup : Ensures (indexLookup [.keypair] (u32le msg 4)) safe
      (fun result g => safe g ∧ ∀owner pid, result = some (owner,pid) → ∃id d p k,
        owner = .keypair id ∧ g.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount ∧
        d.keypairs[id]? = some k ∧ k.peer = some pid ∧ 0 < k.refcount) :=
    indexLookup_keypair_held (u32le msg 4)
  rw [factor]
  refine ensures_bind _ _ hlookup ?_
  intro entry g ambient result final after pre run
  cases entry with
  | none =>
    simp [acquired, afterGet, keypairGetNull, peerPut, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact pre.1
  | some pair =>
    rcases pair with ⟨owner,pid⟩
    obtain ⟨id,d,p,k,ownerEq,device,resident,peerHeld,key,_,keyLive⟩ := pre.2 owner pid rfl
    subst owner
    simp only [acquired, pure_bind] at run
    have keyGet : Ensures (keypairGet (some id)) (fun g => g.dev = some d)
        (fun output g => output = some id ∧ held id pid g) := by
      intro g a out finish inputs before actual
      have outcome := Config.keypairGet_present id d k key g a out finish inputs before actual
      have nonzero : k.refcount ≠ 0 := by omega
      simp only [nonzero, ite_false] at outcome
      refine ⟨outcome.1,Config.withKeypair d id {k with refcount := k.refcount + 1},p,
        {k with refcount := k.refcount + 1},outcome.2,
        keypairAcquire_owner_coherent d id k key (pre.1 d device),resident,peerHeld,?_,by
          change 1 < k.refcount + 1
          omega⟩
      simp [Config.withKeypair]
    have composed : Ensures (do let kp ← keypairGet (some id); afterGet (some pid) kp)
        (fun g => g.dev = some d) (fun _ => safe) := by
      refine ensures_bind _ _ keyGet ?_
      intro kp g a r finish inputs h actual
      rcases h with ⟨rfl,h⟩
      exact hget id pid g a r finish inputs h actual
    exact composed g ambient result final after device run

end Leanux.Proofs.WG.Index
