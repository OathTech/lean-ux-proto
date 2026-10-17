import Leanux.Proofs.WG.Index.RxQueueFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Every normal return of the actual data-ingress path preserves both index-table uniqueness properties and the keypair allocation bound. No ownership coherence, queue consistency, or readiness premise is required. -/
theorem consumeData_tables (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Campaign2.Ensures (consumeData msg src ds) View.TablesSafe (fun _ => View.TablesSafe) := by
  change Ensures (consumeData msg src ds) TablesSafeWG (fun _ => TablesSafeWG)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final after pre run; cases run; exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  have hpeer (pid : PeerId) : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG) g a r final after pre run).1
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final after pre run; cases run
  have hnull : Ensures keypairGetNull TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold keypairGetNull
    exact ensures_bind _ _ (hbranch _ _) (fun _ => hpure _)
  have hnewRx (pkt : RxPacket) : Ensures (newRxSkb pkt) TablesSafeWG (fun _ => TablesSafeWG) :=
    liftSkb_tables (SkbStore.newRx pkt)
  have hfreeRx (id : SkbId) : Ensures (freeRxSkb id) TablesSafeWG (fun _ => TablesSafeWG) :=
    liftSkb_tables (SkbStore.freeRx id)
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
      acquired entry) := by
    rfl
  have hafter (id : KeypairId) (peer : Option PeerId) (skb : SkbId) (ret : Int) :
      Ensures (afterEnqueue id peer skb ret) TablesSafeWG (fun _ => TablesSafeWG) := by
    have hfinish : Ensures (do
        if ← WG.orM (branch .dataEnqueueOk (ret == 0))
            (branch .dataEnqueueOkEpipe (ret == -EPIPE)) then return
        keypairPut (some id) false
        peerPut peer
        freeRxSkb skb) TablesSafeWG (fun _ => TablesSafeWG) := by
      have hor : Ensures (WG.orM (branch .dataEnqueueOk (ret == 0))
          (branch .dataEnqueueOkEpipe (ret == -EPIPE))) TablesSafeWG (fun _ => TablesSafeWG) := by
        unfold WG.orM
        refine ensures_bind _ _ (hbranch _ _) ?_
        intro ok
        cases ok with
        | false => exact hbranch _ _
        | true => exact hpure _
      refine ensures_bind _ _ hor ?_
      intro done
      cases done with
      | true => exact hpure ()
      | false =>
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (keypairPut_tables (some id) false)) ?_
        intro _
        exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (peerPut_tables peer)) (fun _ => hfreeRx skb)
    unfold afterEnqueue
    refine ensures_bind _ _ (hbranch .dataEpipe (ret == -EPIPE)) ?_
    intro pipe
    cases pipe with
    | false => exact hfinish
    | true => exact ensures_bind (Q := fun _ => TablesSafeWG) _ _ (enqueuePerPeerRx_pure_spec_tables_variant skb .dead) (fun _ => hfinish)
  have hwith (id : KeypairId) (pid : PeerId) (peer : Option PeerId) :
      Ensures (withKey id pid peer) TablesSafeWG (fun _ => TablesSafeWG) := by
    simp only [withKey]
    refine ensures_bind _ _ (hpeer pid) ?_
    intro p
    refine ensures_bind _ _ (hbranch .dataPeerDead p.isDead) ?_
    intro dead
    cases dead with
    | true =>
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (keypairPut_tables (some id) false)) ?_
      intro _
      exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (peerPut_tables peer)) (fun _ => hpure ())
    | false =>
      refine ensures_bind _ _ (hnewRx _) ?_
      intro skb
      exact ensures_bind (Q := fun _ => TablesSafeWG) _ _ (enqueuePerDeviceAndPeerRx_spec_tables_variant skb) (hafter id peer skb)
  have hget (peer : Option PeerId) (kp : Option KeypairId) :
      Ensures (afterGet peer kp) TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold afterGet
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro absent
    cases absent with
    | false =>
      cases kp with
      | none => exact hstop _
      | some id =>
        cases peer with
        | none => exact hstop _
        | some pid => exact hwith id pid (some pid)
    | true =>
      exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (peerPut_tables peer)) (fun _ => hpure ())
  have hentry (entry : Option (IndexOwner × PeerId)) :
      Ensures (acquired entry) TablesSafeWG (fun _ => TablesSafeWG) := by
    cases entry with
    | none =>
      simp only [acquired, pure_bind]
      exact ensures_bind _ _ hnull (fun _ => hget none none)
    | some pair =>
      rcases pair with ⟨owner, pid⟩
      cases owner with
      | keypair id =>
        simp only [acquired, pure_bind]
        exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (keypairGet_tables (some id)))
          (fun kp => hget (some pid) kp)
      | handshake id =>
        intro g a r final after pre run
        cases run
  rw [factor]
  exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (indexLookup_tables _ _)) hentry

end Leanux.Proofs.WG.Index
