import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPointSource

/-! Canonical witnesses expand the actual take, key acquisition, checked
nonce traversal, restore and keepalive source. The original action remains
the index of each witness, including every early return and Stop arm. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal
open Staged.Obligations HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000

noncomputable def takeShape (pid : PeerId) : Shape (liftWGPrefix (Take.takePrefix pid)) := by
  apply Shape.marked (.take pid)
  unfold Take.takePrefix
  rw [lift_bind]
  apply Shape.bind (.native (.peer pid))
  intro peer
  rw [lift_bind]
  apply Shape.bind (.native (.branch .stagedEmpty peer.staged.isEmpty))
  intro empty
  cases empty <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [lift_bind]
    exact .bind (.native (.setPeer pid {peer with staged:=[]})) (fun _=>by rw [lift_pure]; exact .pure _)
  · rw [lift_pure]; exact .pure _

noncomputable def keyShape (key : Option KeypairId) : Shape (liftWGPrefix (keypairGet key)) := by
  apply Shape.marked (.keyBorrow key)
  unfold keypairGet
  rw [lift_bind]
  apply Shape.bind (.native (.branch .keypairGetNull key.isNone))
  intro missing
  cases missing <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · cases key with
    | none=>exact .native (.invariant _)
    | some kid=>
      rw [lift_bind]
      apply Shape.bind (.native (.key kid))
      intro key
      simp only [lift_bind]
      apply Shape.bind (.native (.incNotZero key.refcount))
      intro nonzero
      apply Shape.bind (.native (.branch .keypairGetZero (!nonzero)))
      intro zero
      cases zero <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · rw [lift_bind]
        exact .bind (.native (.setKey kid {key with refcount:=key.refcount+1})) (fun _=>by rw [lift_pure]; exact .pure _)
      · rw [lift_pure]; exact .pure _
  · rw [lift_pure]; exact .pure _

noncomputable def borrowShape (taken : Option Peer) : Shape (liftWGPrefix (Take.borrow taken)) := by
  apply Shape.marked (.borrow taken)
  cases taken with
  | none=>change Shape (liftWGPrefix (pure none)); rw [lift_pure]; exact .pure _
  | some peer=>
    unfold Take.borrow
    rw [lift_bind]
    exact .bind (keyShape peer.keypairCurrent) (fun _=>by rw [lift_pure]; exact .pure _)

noncomputable def selectionShape (pid : PeerId) : Shape (CausalJournal.selection pid) := by
  apply Shape.marked (.selection pid)
  change Shape (receiptWGObserved (Take.observed Event.stagingTaken pid) _)
  apply Shape.receipt
  unfold Take.observed
  exact .bind (.receipt _ (takeShape pid)) borrowShape

noncomputable def walkShape (pid : PeerId) (kid : KeypairId) (remaining : List Packet)
    (packets : List DataPacket) :
    Shape (walkWith liftWGPrefix (fun key=>state (Journal.reserve key)) pid kid remaining packets) := by
  apply Shape.marked (.nonce pid kid remaining packets)
  cases remaining with
  | nil=>exact .bind (.native (.branch .stagedNonceIterate false)) (fun _=>.pure _)
  | cons packet rest=>
    unfold walkWith
    apply Shape.bind (.native (.branch .stagedNonceIterate true))
    intro _
    apply Shape.bind (.native (.ecn packet))
    intro ds
    apply Shape.bind (.child (.reserve kid))
    intro nonce
    apply Shape.bind (.native (.compare .stagedNonceRejected (nonce≥REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES))
    intro over
    cases over <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact walkShape pid kid rest _
    · exact .pure _

noncomputable def guardsShape (pid : PeerId) (peer : Peer) (key : Option KeypairId) :
    Shape (checkedPrefix pid peer key) := by
  apply Shape.marked (.guards pid peer key)
  unfold checkedPrefix prefixWith
  apply Shape.bind (.native (.branch .stagedNoKeypair key.isNone))
  intro missing
  cases missing <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · cases key with
    | none=>exact .pure _
    | some kid=>
      apply Shape.bind (.native (.key kid))
      intro key
      apply Shape.bind (.native (.branch .stagedKeyInvalid (!key.sending.isValid)))
      intro invalid
      cases invalid
      · apply Shape.bind (.native (.age key.sending.birthdate))
        intro expired
        cases expired <;> simp only [Bool.false_eq_true,ite_false,ite_true]
        · exact walkShape pid kid peer.staged []
        · exact .pure _
      · exact .pure _
  · exact .pure _

noncomputable def acquireShape (pid : PeerId) : Shape (liftWGPrefix (peerGet pid)) := by
  apply Shape.marked (.acquire pid)
  unfold peerGet
  simp only [lift_bind]
  exact .bind (.native (.notPending pid)) (fun _=>
    .bind (.native (.peer pid)) (fun peer=>
      .bind (.native (.inc peer.refcount)) (fun _=>.native (.setPeer pid {peer with refcount:=peer.refcount+1}))))

noncomputable def allocationPrefixShape (pid : PeerId) (peer : Peer) (key : Option KeypairId) :
    Shape (allocationPrefix pid peer key) := by
  unfold allocationPrefix
  apply Shape.bind (guardsShape pid peer key)
  intro decision
  cases decision with
  | rejected _ _=>exact .pure _
  | unreachable=>exact .pure _
  | submit kid packets=>exact .bind (.native (.owner kid)) (fun owner=>
      .bind (acquireShape owner) (fun _=>.pure _))

noncomputable def restoreShape (pid : PeerId) (packets : List Packet) :
    Shape (CausalJournal.stagedRestore pid packets) := by
  apply Shape.marked (.restore pid packets)
  change Shape (receiptWGObserved (liftWGPrefix (Restore.nativeRestore pid packets)) _)
  apply Shape.receipt
  unfold Restore.nativeRestore
  simp only [lift_bind]
  exact .bind (.native (.peer pid)) (fun cached=>
    .bind (.native (.peer pid)) (fun queued=>.native (.setPeer pid {cached with staged:=packets++queued.staged})))

noncomputable def orphanShape (packets : List Packet) : Shape (do
    for _ in packets do _ ← liftWGPrefix (branch .stagedOrphanWalk true)
    _ ← liftWGPrefix (branch .stagedOrphanWalk false)) := by
  apply Shape.bind
  · exact listShape packets PUnit.unit _ (fun _ _=>.bind (.native (.branch .stagedOrphanWalk true)) (fun _=>.pure _))
  · intro _; exact .bind (.native (.branch .stagedOrphanWalk false)) (fun _=>.pure _)

noncomputable def rejectPrefixShape (packets : List Packet) (key : Option KeypairId) (invalid : Bool) :
    Shape (RestoreEntry.prefixWith liftWGPrefix packets key invalid) := by
  unfold RestoreEntry.prefixWith
  cases invalid <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact .bind (.child (.repayment key)) (fun _=>orphanShape packets)
  · cases key with
    | none=>exact .bind (.native (.invariant Unit)) (fun _=>
        .bind (.child (.repayment none)) (fun _=>orphanShape packets))
    | some kid=>exact .bind (.native (.key kid)) (fun key=>
        .bind (.native (.setKey kid {key with sending:={key.sending with isValid:=false}})) (fun _=>
          .bind (.child (.repayment (some kid))) (fun _=>orphanShape packets)))

noncomputable def rejectedShape (pid : PeerId) (peer : Peer) (key : Option KeypairId) (invalid : Bool) :
    Shape (HeldSource.noKey pid peer key invalid) := by
  apply Shape.marked (.rejected pid peer key invalid)
  unfold HeldSource.noKey
  rw [RestoreEntry.no_key_factor]
  exact .bind (rejectPrefixShape peer.staged key invalid) (fun _=>
    .bind (restoreShape pid peer.staged) (fun _=>.child (.queued pid)))

noncomputable def tailShape (pid : PeerId) (peer : Peer) (decision : Decision) :
    Shape (allocationTail pid peer decision) := by
  apply Shape.marked (.submit pid peer decision)
  cases decision with
  | rejected key invalid=>exact rejectedShape pid peer key invalid
  | unreachable=>exact .native (.invariant _)
  | submit kid packets=>exact .bind (.child (.allocate packets)) (fun items=>.child (.create pid items))

noncomputable def chosenShape (pid : PeerId) : (chosen : Option (Peer×Option KeypairId)) →
    Shape (match chosen with
      | none=>pure ()
      | some (peer,key)=>allocationPrefix pid peer key >>= allocationTail pid peer)
  | none=>.pure ()
  | some (peer,key)=>.bind (allocationPrefixShape pid peer key) (tailShape pid peer)

noncomputable def stagingShape (pid : PeerId) : Shape (Driver.stagingObserved hooks pid) :=
  .marked (.staging pid) ((allocation_factor pid).symm ▸
    Shape.bind (selectionShape pid) (chosenShape pid))

noncomputable def preparationShape (pid : PeerId) : Shape (CausalJournal.keepalivePrepare pid) := by
  change Shape (receiptWGObserved (liftWGPrefix (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid)) _)
  apply Shape.receipt
  unfold RetirementSecurity.OccurrenceHandshake.keepalivePrepare
  simp only [lift_bind]
  apply Shape.bind (.native (.peer pid))
  intro peer
  apply Shape.bind (.native (.branch .keepaliveStagedEmpty peer.staged.isEmpty))
  intro empty
  cases empty <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [lift_pure]; exact .pure _
  · simp only [lift_bind]
    apply Shape.bind (.native .allocation)
    intro allocated
    apply Shape.bind (.native (.branch .keepaliveNoMem (!allocated)))
    intro refused
    cases refused <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · simp only [lift_bind]
      exact .bind (.native .device) (fun d=>.bind (.native (.setPeer pid {peer with staged:=peer.staged++[{mtu:=d.mtu}]})) (fun _=>by rw [lift_pure]; exact .pure _))
    · rw [lift_pure]; exact .pure _

noncomputable def keepaliveShape (pid : PeerId) : Shape (Driver.keepaliveObserved hooks pid) := by
  apply Shape.marked (.keepalive pid)
  unfold Driver.keepaliveObserved
  apply Shape.bind (preparationShape pid)
  intro ready
  cases ready <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact .pure _
  · exact stagingShape pid

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
