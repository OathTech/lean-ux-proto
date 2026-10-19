import Leanux.Proofs.WG.TransmitSecurity.StagedObligationHeldFrontier

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.HeldFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Staged.Origins AuthenticatedEffects CausalJournal

theorem suffix_progress {action : WGPrefix Event α}
    (quiet : StateHistoryFrame blocking? action)
    (position : (runPrefix (action.run w) a history).2 = history ++ suffix) :
    ∀ event ∈ suffix, progress event = true := by
  have same := quiet w a history
  rw [position,List.filterMap_append] at same
  have empty : suffix.filterMap blocking? = [] := by
    have sizes := congrArg List.length same
    cases found : suffix.filterMap blocking? with
    | nil => rfl
    | cons x xs => simp only [List.length_append,found,List.length_cons] at sizes; omega
  intro event member
  cases allowed : progress event with
  | true => rfl
  | false =>
    have present : event ∈ suffix.filterMap blocking? :=
      List.mem_filterMap.mpr ⟨event,member,by simp [blocking?,allowed]⟩
    rw [empty] at present
    cases present

variable {Safe : List Event → Prop}
variable (frontier : ∀ h, Anchor ledger debts generation pid peer position h → Safe h)

include frontier in
theorem held_observed {action : WGPrefix Event α} {native : WG.M α}
    (appends : StateAppends action) (quiet : StateHistoryFrame blocking? action)
    (erases : ErasesStatePrefix action native)
    (epoch : SameView Packets.epoch native) (queues : SameView stagedAt native)
    (cells : SameView PacketMaterial.view native) :
    StatePrefixPreserves (Held ledger debts generation pid peer position) Safe action := by
  intro w a h before
  obtain ⟨suffix,extended⟩ := appends w a h
  have allowed := suffix_progress quiet extended
  refine ⟨suffix,extended,?_,?_⟩
  · rw [extended]
    exact frontier _ (before.anchor.append allowed)
  · cases outcome : (runPrefix (action.run w) a h).1 with
    | error stop => trivial
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      have run : (native.run w).run a = .ok ((value,v),b) := (erases w a h).symm.trans outcome
      rw [extended]
      exact before.views_append suffix allowed
        ((ProjectedAction.iff_run_ambient _ _ _).mp epoch w a value v b run)
        ((ProjectedAction.iff_run_ambient _ _ _).mp queues w a value v b run)
        ((ProjectedAction.iff_run_ambient _ _ _).mp cells w a value v b run)

include frontier in
theorem held_lift (action : WG.M α) (epoch : SameView Packets.epoch action)
    (queues : SameView stagedAt action) (cells : SameView PacketMaterial.view action) :
    StatePrefixPreserves (Held ledger debts generation pid peer position) Safe (liftWGPrefix action) :=
  held_observed frontier (StateAppends.lift _) (fun _ _ _ => rfl)
    (erasesStatePrefix_lift _) epoch queues cells

include frontier in
theorem held_world (action : WG.M α) (same : SameView id action) :
    StatePrefixPreserves (Held ledger debts generation pid peer position) Safe (liftWGPrefix action) :=
  held_lift frontier action (same.factor Packets.epoch) (same.factor stagedAt) (same.factor PacketMaterial.view)

include frontier in
theorem held_ambient (action : AmbientM α) :
    StatePrefixPreserves (Held ledger debts generation pid peer position) Safe
      (liftWGPrefix (monadLift action : WG.M α)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => frontier _ before.anchor)
  intro h w a value v b before run
  have kept := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient action (fun w => Held ledger debts generation pid peer position h w a))
    w a value v b before run
  exact ⟨kept.core,kept.vacant,kept.aligned,kept.anchor⟩

include frontier in
theorem held_pure (value : α) :
    StatePrefixPreserves (Held ledger debts generation pid peer position) Safe (pure value) :=
  StatePrefixEnsures.pure _ (fun _ _ _ before => frontier _ before.anchor) (fun _ _ _ before => before)

theorem key_read_material (kid : KeypairId) : SameView PacketMaterial.view (getKeypair kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a key v b run
  exact congrArg PacketMaterial.view (KeyTimes.getKeypair_return kid w v key a b run).1

theorem key_write_material (kid : KeypairId) (key : Keypair) :
    SameView PacketMaterial.view (setKeypair kid key) :=
  PacketMaterial.modify_device _ (fun _ => rfl)

include frontier in
theorem held_read_key (kid : KeypairId) :
    StatePrefixPreserves (Held ledger debts generation pid peer position) Safe (liftWGPrefix (getKeypair kid)) :=
  held_lift frontier _ (PacketOrigins.epoch_ring (TxRing.getKeypair_frame kid)) (Exact.read_key kid)
    (key_read_material kid)

include frontier in
theorem held_write_key (kid : KeypairId) (key : Keypair) :
    StatePrefixPreserves (Held ledger debts generation pid peer position) Safe (liftWGPrefix (setKeypair kid key)) :=
  held_lift frontier _ (key_write_epoch kid key) (set_key_staged kid key) (key_write_material kid key)

include frontier in
theorem held_key_put (kid : Option KeypairId) :
    StatePrefixPreserves (Held ledger debts generation pid peer position) Safe (liftWGPrefix (keypairPut kid false)) :=
  held_lift frontier _ (PacketOrigins.epoch_ring (TxRing.keypairPut_frame kid false)) (Exact.key_put kid false)
    (PacketMaterial.of_packets (TxDisposition.keyPut_packets kid false))

include frontier in
theorem held_key_get (kid : Option KeypairId) :
    StatePrefixPreserves (Held ledger debts generation pid peer position) Safe (liftWGPrefix (keypairGet kid)) :=
  held_lift frontier _ (PacketOrigins.epoch_ring ((RetirementSecurity.keyGet_cryptWire kid).factor Prod.fst))
    (key_get_staged kid) (PacketMaterial.of_packets ((RetirementSecurity.keyGet_cryptWire kid).factor Prod.snd))

include frontier in
theorem reservation_held (kid : KeypairId) :
    StatePrefixPreserves (Held ledger debts generation pid peer position) Safe (state (Journal.reserve kid)) := by
  have quiet : StateHistoryFrame blocking? (state (Journal.reserve kid)) := by
    apply Origins.focused_history_frame _ _ blocking? _ ((StateAppends.focus _ _ _).receiptWGObserved _)
    exact StateHistoryFrame.receiptWGObserved
      (fun w => focusPrefix_other _ _ _ (fun _ => rfl) ((Nonce.reserveObserved kid).run w)) _ (fun _ => rfl)
  have cells : SameView PacketMaterial.view (Nonce.reserveNative kid) :=
    SameView.bind (key_read_material kid) (fun key =>
      SameView.bind (key_write_material kid _) (fun _ => SameView.pure _ key.sendingCounter))
  exact held_observed frontier (StateAppends.focus _ _ _) quiet (reserve_erases kid)
    (reserve_epoch kid) (reserve_staged kid) cells

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.HeldFrontier
