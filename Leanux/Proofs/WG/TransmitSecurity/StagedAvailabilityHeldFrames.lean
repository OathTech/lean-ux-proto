import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityObserved

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem suffix_quiet {action : WGPrefix Event α}
    (quiet : StateHistoryFrame allocation? action)
    (position : (runPrefix (action.run w) a h).2 = h ++ suffix) :
    ∀ event ∈ suffix, allocation? event = none := by
  have same := quiet w a h
  rw [position,List.filterMap_append] at same
  have empty : suffix.filterMap allocation? = [] := by
    have sizes := congrArg List.length same
    cases found : suffix.filterMap allocation? with
    | nil => rfl
    | cons x xs => simp only [List.length_append,found,List.length_cons] at sizes; omega
  intro event member
  cases found : allocation? event with
  | none => rfl
  | some value =>
    have present := List.mem_filterMap.mpr ⟨event,member,found⟩
    rw [empty] at present
    cases present

theorem state_quiet {action : WGPrefix Event α} {native : WG.M α}
    (appends : StateAppends action) (quiet : StateHistoryFrame allocation? action)
    (erase : ErasesStatePrefix action native) (kept : ∀ h, Preserves (Inv h) native) :
    StateSafe action := by
  intro w a h before
  obtain ⟨suffix,position⟩ := appends w a h
  have excluded := suffix_quiet quiet position
  have safe : Safe (runPrefix (action.run w) a h).2 := by
    rw [position]
    exact before.2.quiet excluded
  refine ⟨suffix,position,safe,?_⟩
  cases outcome : (runPrefix (action.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have run : (native.run w).run a = .ok ((value,v),b) := (erase w a h).symm.trans outcome
    have inv := (hoare_iff_run_ambient _ _ _).mp (kept h) w a value v b before.1 run
    refine ⟨?_,safe⟩
    rw [position]
    exact inv.append (fun _ event member => no_use (excluded event member))

theorem Saved.views (saved : Saved h pid peer w)
    (epoch : Packets.epoch v = Packets.epoch w) (queues : stagedAt v = stagedAt w) :
    Saved h pid peer v := by
  obtain ⟨generation,atEpoch,empty,batch⟩ := saved
  exact ⟨generation,epoch.trans atEpoch,by rw [queues]; exact empty,batch⟩

theorem StateSafe.saved (safe : StateSafe action) (erase : ErasesStatePrefix action native)
    (quiet : StateHistoryFrame allocation? action)
    (epoch : SameView Packets.epoch native) (queues : SameView stagedAt native) :
    StatePrefixPreserves (Held pid peer) Safe action := by
  intro w a h before
  obtain ⟨suffix,position,history,after⟩ := safe w a h before.1
  have excluded := suffix_quiet quiet position
  refine ⟨suffix,position,history,?_⟩
  cases outcome : (runPrefix (action.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have run : (native.run w).run a = .ok ((value,v),b) := (erase w a h).symm.trans outcome
    have saved := before.2.views
      ((ProjectedAction.iff_run_ambient _ _ _).mp epoch w a value v b run)
      ((ProjectedAction.iff_run_ambient _ _ _).mp queues w a value v b run)
    refine ⟨by simpa only [outcome] using after,?_⟩
    rw [position]
    exact saved.append (fun event member => no_use (excluded event member))

theorem held_frame (action : WG.M α)
    (epoch : SameView Packets.epoch action) (queues : SameView stagedAt action) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix action) :=
  (state_lift action (fun _ => frame epoch (Staged.of_view _ queues))).saved
    (erasesStatePrefix_lift _) (fun _ _ _ => rfl) epoch queues

theorem held_read_key (kid : KeypairId) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix (getKeypair kid)) :=
  held_frame _ (PacketOrigins.epoch_ring (TxRing.getKeypair_frame kid)) (Exact.read_key kid)

theorem held_write_key (kid : KeypairId) (key : Keypair) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix (setKeypair kid key)) :=
  held_frame _ (Origins.key_write_epoch kid key) (Origins.set_key_staged kid key)

theorem held_key_put (kid : Option KeypairId) (now : Bool) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix (keypairPut kid now)) :=
  held_frame _ (PacketOrigins.epoch_ring (TxRing.keypairPut_frame kid now)) (Exact.key_put kid now)

theorem held_peer_get (target : PeerId) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix (peerGet target)) :=
  held_frame _ (PacketOrigins.epoch_ring (TxRing.peerGet_frame target)) (Exact.peer_get target)

theorem held_ambient (action : AmbientM α) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix (monadLift action : WG.M α)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => before.1.2)
  intro h w a value v b before run
  exact (hoare_iff_run_ambient _ _ _).mp (hoare_liftAmbient action (fun w => Held pid peer h w a))
    w a value v b before run

theorem held_world (action : WG.M α) (unchanged : SameView id action) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix action) :=
  held_frame action (unchanged.factor Packets.epoch) (unchanged.factor stagedAt)

theorem reserve_observed (kid : KeypairId) :
    StatePrefixPreserves (Held pid peer) Safe (state (Journal.reserve kid)) := by
  have quiet : StateHistoryFrame allocation? (state (Journal.reserve kid)) := by
    apply Origins.focused_history_frame _ _ allocation? _
      ((StateAppends.focus _ _ _).receiptWGObserved _)
    exact StateHistoryFrame.receiptWGObserved
      (fun w => focusPrefix_other _ _ _ (fun _ => rfl) ((Nonce.reserveObserved kid).run w)) _ (fun _ => rfl)
  have native (h) : Preserves (Inv h) (Nonce.reserveNative kid) :=
    frame (Origins.reserve_epoch kid) (Staged.of_view _ (Origins.reserve_staged kid))
  exact (state_quiet (StateAppends.focus _ _ _) quiet (Origins.reserve_erases kid) native).saved
    (Origins.reserve_erases kid) quiet (Origins.reserve_epoch kid) (Origins.reserve_staged kid)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
