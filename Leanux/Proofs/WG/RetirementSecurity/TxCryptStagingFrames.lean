import Leanux.Proofs.WG.RetirementSecurity.TxCryptWorker
import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceStaging

/-! The native staging prefix changes keys and staged plaintext without
altering queued TX ownership or pending encryption. Saved peer reads retain
the queue value needed by the original restaging setter. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

private theorem queue_read_bind (initial : PeerId → Option (List (List SkbId)))
    (pid : PeerId) (f : Peer → WG.M α)
    (next : ∀ p, initial pid = some p.txQueue.all →
      Preserves (fun w => handoffTxView w = initial) (f p)) :
    Preserves (fun w => handoffTxView w = initial) (getPeer pid >>= f) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,tail⟩ := run
  obtain ⟨same,clock,d,device,stored⟩ := Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  have named : initial pid = some p.txQueue.all := by
    rw [← before]
    simp [handoffTxView,device,stored]
  exact (hoare_iff_run_ambient _ _ _).mp (next p named) w a result v b before tail

private theorem queue_set_saved (initial : PeerId → Option (List (List SkbId)))
    (pid : PeerId) (p : Peer) (saved : initial pid = some p.txQueue.all) :
    Preserves (fun w => handoffTxView w = initial) (setPeer pid p) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases device : w.dev with
  | none => simp [← before,handoffTxView,device] at saved
  | some d =>
    cases run
    funext other
    by_cases same : pid = other
    · subst other
      simpa [handoffTxView,modifyDev,device] using saved.symm
    · simpa [handoffTxView,modifyDev,device,Std.TreeMap.getElem?_insert,same] using congrFun before other

private theorem queue_modify (initial) (f : Device → Device)
    (peers : ∀ d, (f d).peers = d.peers) :
    Preserves (fun w => handoffTxView w = initial) (modifyDev f) := by
  apply hoare_modify
  intro w before
  change (fun pid => handoffTxView _ pid) = initial
  change (fun pid => handoffTxView w pid) = initial at before
  simpa only [handoffTxView,Option.bind_map,Function.comp_def,peers] using before

macro "crypt_queue_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (env_bind_head getPeer; apply queue_read_bind $initial; intro p saved)
  | (rx_retention_head setPeer; apply queue_set_saved $initial; assumption)
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getKeypair
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a k v b before run
     exact (KeyTimes.getKeypair_return _ w v k a b run).1 ▸ before)
  | (rx_retention_head setKeypair; unfold setKeypair)
  | (rx_retention_head modifyDev; apply queue_modify $initial; intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head branchExpired
     exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => handoffTxView w = $initial))
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (fun w => handoffTxView w = $initial)
     intro x b
     change Preserves (fun w => handoffTxView w = $initial) _)
  | rx_retention_step)

theorem keyGet_cryptWire (kid : Option KeypairId) : SameView txCryptWire (keypairGet kid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' crypt_wire_step initial

theorem keyGet_tx_queues (kid : Option KeypairId) : SameView handoffTxView (keypairGet kid) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' crypt_queue_step initial

theorem noKey_cryptWire (pid : PeerId) (packets : List WG.Packet)
    (key : Option KeypairId) (invalid : Bool) :
    SameView txCryptWire (stagedOutNokey pid packets key invalid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold stagedOutNokey
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head keypairPut
       exact ((TxRing.keypairPut_frame _ _).product (TxDisposition.keyPut_packets _ _)).wp (· = initial))
    | (rx_retention_head sendQueuedHandshakeInitiation
       exact (sendQueued_cryptWire _ _).wp (· = initial))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => txCryptWire w = initial)
       intro x b
       change Preserves (fun w => txCryptWire w = initial) _)
    | crypt_wire_step initial

theorem noKey_tx_queues (pid : PeerId) (packets : List WG.Packet)
    (key : Option KeypairId) (invalid : Bool) :
    SameView handoffTxView (stagedOutNokey pid packets key invalid) := by
  have keyPut (kid : Option KeypairId) (now : Bool) : SameView handoffTxView (keypairPut kid now) :=
    (keypairPut_protect kid now).factor (fun fields => fields.2.2.1)
  have queued (peer : PeerId) (retry : Bool) : SameView handoffTxView (sendQueuedHandshakeInitiation peer retry) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    exact ownership_points_queues ((ProjectedAction.iff_run_ambient _ _ _).mp
      (sendQueued_ownership peer retry) w a result v b run)
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold stagedOutNokey
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head keypairPut; exact (keyPut _ _).wp (· = initial))
    | (rx_retention_head sendQueuedHandshakeInitiation; exact (queued _ _).wp (· = initial))
    | crypt_queue_step initial

theorem crypt_passive {action : WG.M α} (wire : SameView txCryptWire action)
    (queues : SameView handoffTxView action) : Preserves (TxCryptInventory active) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp wire w a result v b run
  have owners := (ProjectedAction.iff_run_ambient _ _ _).mp queues w a result v b run
  exact before.frame_packets (congrArg Prod.fst fields) (fun _ owned => owned.queues owners)
    (congrArg Prod.snd fields)

theorem crypt_key_get (kid : Option KeypairId) : Preserves (TxCryptInventory active) (keypairGet kid) :=
  crypt_passive (keyGet_cryptWire kid) (keyGet_tx_queues kid)

theorem crypt_no_key (pid : PeerId) (packets : List WG.Packet)
    (key : Option KeypairId) (invalid : Bool) :
    Preserves (TxCryptInventory active) (stagedOutNokey pid packets key invalid) :=
  crypt_passive (noKey_cryptWire pid packets key invalid) (noKey_tx_queues pid packets key invalid)

end Leanux.Proofs.WG.RetirementSecurity
