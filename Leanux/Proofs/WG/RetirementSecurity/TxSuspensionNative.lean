import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionFrames

/-! Actual WG stores and reference operations leave suspended TX actors
intact. These proofs retain Ambient through native branch records and exact
component adapters, rather than assuming all ambient code is passive. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem invariant (message : String) : Keeps (Leanux.invariant message : StateT S AmbientM α) := by
  apply ambient
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run

theorem unsupported (message : String) : Keeps (Leanux.unsupported message : StateT S AmbientM α) := by
  apply ambient
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run

theorem branch (decision : Decision) (value : Bool) :
    Keeps (Leanux.branch decision value : StateT S AmbientM Bool) := by
  apply ambient
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

theorem compare (decision : Decision) (value : Bool) (a b : Int) :
    Keeps (branchCmp decision value a b : StateT S AmbientM Bool) := by
  apply ambient
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

theorem hidden (site : HiddenSite) : Keeps (Leanux.hidden site : StateT S AmbientM (List UInt8)) :=
  ambient (TxActorFrames.hidden site)

theorem device : Keeps getDev := by
  unfold getDev
  repeat' first | env_operation_fact invariant | suspension_step

theorem modify_device (f : Device→Device) : Keeps (modifyDev f) := modify _

theorem peer (pid : PeerId) : Keeps (getPeer pid) := by
  unfold getPeer
  repeat' first | env_operation_fact device | env_operation_fact invariant | suspension_step

theorem key (kid : KeypairId) : Keeps (getKeypair kid) := by
  unfold getKeypair
  repeat' first | env_operation_fact device | env_operation_fact invariant | suspension_step

theorem set_peer (pid : PeerId) (p : Peer) : Keeps (setPeer pid p) := modify_device _

theorem set_key (kid : KeypairId) (k : Keypair) : Keeps (setKeypair kid k) := modify_device _

theorem index_lift {action : IndexM α} (frame : Keeps action) : Keeps (liftIndex action) := by
  unfold liftIndex
  apply bind device
  intro d
  apply bind (ambient (frame d.indexTable))
  rintro ⟨value,table⟩
  exact bind (modify_device _) (fun _=>pure value)

theorem skb_lift {action : SkbM α} (frame : Keeps action) : Keeps (liftSkb action) := by
  unfold liftSkb
  apply bind device
  intro d
  apply bind (ambient (frame {txSkbs:=d.txSkbs,rxSkbs:=d.rxSkbs,nextSkb:=d.nextSkb}))
  rintro ⟨value,store⟩
  exact bind (modify_device _) (fun _=>pure value)

theorem packet (skb : SkbId) : Keeps (getTxSkb skb) := by
  apply skb_lift
  unfold SkbStore.getTx
  repeat' first | env_operation_fact invariant | suspension_step

theorem free_packet (skb : SkbId) : Keeps (freeTxSkb skb) := by
  apply skb_lift
  unfold SkbStore.freeTx
  apply bind
  · unfold SkbStore.getTx
    repeat' first | env_operation_fact invariant | suspension_step
  · intro _; exact modify _

theorem set_packet (skb : SkbId) (f : DataPacket→DataPacket) : Keeps (setTxSkb skb f) := by
  apply skb_lift
  unfold SkbStore.setTx
  have read : Keeps (SkbStore.getTx skb) := by
    unfold SkbStore.getTx
    repeat' first | env_operation_fact invariant | suspension_step
  repeat' first | env_operation_fact read | suspension_step

theorem index_remove (owner : IndexOwner) : Keeps (indexRemove owner) := by
  unfold indexRemove
  change Keeps (do
    let table←(MonadStateOf.get : IndexM (List IndexEntry))
    _←Leanux.branch .idxRemoveHashed (table.any (·.owner == owner))
    _root_.modify fun t : List IndexEntry=>t.filter fun e=> !(e.owner == owner) : IndexM Unit)
  repeat' first | env_operation_fact branch | suspension_step

theorem owner_word (owner : IndexOwner) : Keeps owner.peerWord := by
  cases owner <;> unfold IndexOwner.peerWord
  all_goals repeat' first | env_operation_fact peer | env_operation_fact key | suspension_step

theorem owner_deref (owner : IndexOwner) : Keeps (IndexOwner.peerDeref owner) := by
  unfold IndexOwner.peerDeref
  repeat' first | env_operation_fact owner_word | env_operation_fact unsupported | suspension_step

theorem modify_ambient (f : Ambient→Ambient) (same : ∀a,(f a).suspended=a.suspended) :
    Keeps (modifyAmbient f : StateT S AmbientM Unit) := by
  apply ambient
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  exact same w

theorem refcount_dec (count : Nat) : Keeps (refcountDecAndTest count : StateT S AmbientM Bool) := by
  suspension_source [refcountDecAndTest] using [branch,compare,unsupported]

theorem refcount_inc (count : Nat) : Keeps (refcountInc count : StateT S AmbientM Unit) := by
  suspension_source [refcountInc] using [branch,compare,unsupported]

theorem peer_get (pid : PeerId) : Keeps (peerGet pid) := by
  suspension_source [peerGet,requireNotPending] using [peer,refcount_inc,set_peer]

theorem retire_peer (pid : PeerId) : Keeps (retirePeerUnits pid) := by
  unfold retirePeerUnits
  apply bind
  · apply modify_ambient
    intro a
    rfl
  · intro _
    exact modify _

theorem index_remove_lift (owner : IndexOwner) :
    Keeps (monadLift (indexRemove owner) : WG.M Unit) := index_lift (index_remove owner)

theorem peer_put (owner : Option PeerId) : Keeps (peerPut owner) := by
  suspension_source [peerPut,requireNotPending] using [branch,invariant,peer,set_peer,refcount_dec,index_remove_lift,modify_device,retire_peer]

theorem key_put (kid : Option KeypairId) (now : Bool) : Keeps (keypairPut kid now) := by
  suspension_source [keypairPut] using [branch,invariant,key,set_key,owner_deref,refcount_dec,index_remove_lift,modify_device]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
