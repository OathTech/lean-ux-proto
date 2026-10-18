import Leanux.Proofs.WG.RetirementSecurity.OccurrencePeerRemoval

/-! Fresh peer creation retains every existing TX owner. The native chosen
frontier slot is empty by the independently maintained allocation bound;
no vacant-slot premise is passed to the original-operation contract. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceCreation
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits OccurrenceStack OccurrenceHandshake

theorem precompute_wire (pid : PeerId) : SameView txCryptWire (precomputeStaticStatic pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold precomputeStaticStatic requireNotPending
  simp (config := {zeta := false}) only [branch]
  repeat' occurrence_handshake_wire initial

theorem precompute_contents (pid : PeerId) : SameView txQueueContents (precomputeStaticStatic pid) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold precomputeStaticStatic requireNotPending
  simp (config := {zeta := false}) only [branch]
  repeat' occurrence_handshake_contents initial

theorem handshake_init_wire (pid : PeerId) (psk : Option Key) : SameView txCryptWire (handshakeInit pid psk) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold handshakeInit IndexOwner.setPeerWord
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head precomputeStaticStatic; exact (precompute_wire _).wp (· = initial))
    | occurrence_handshake_wire initial

theorem handshake_init_contents (pid : PeerId) (psk : Option Key) : SameView txQueueContents (handshakeInit pid psk) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold handshakeInit IndexOwner.setPeerWord
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head precomputeStaticStatic; exact (precompute_contents _).wp (· = initial))
    | occurrence_handshake_contents initial

theorem reset_wire (pid : PeerId) : SameView txCryptWire (resetLastSentHandshake pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold resetLastSentHandshake
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' occurrence_handshake_wire initial

theorem reset_contents (pid : PeerId) : SameView txQueueContents (resetLastSentHandshake pid) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold resetLastSentHandshake
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' occurrence_handshake_contents initial

theorem core_wire (pid : PeerId) (key : Key) : SameView txCryptWire (Peers.peerCreateCore pid key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  rw [Peers.peerCreateCore_run] at run
  cases run
  simp only [Peers.creationCoreWorld,txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,
    Option.map_map,Option.bind_map,Function.comp_def]

private theorem core_contents (initial : PeerId → List (List SkbId)) (pid : PeerId) (key : Key)
    (empty : initial pid = []) :
    Preserves (fun w => txQueueContents w = initial) (Peers.peerCreateCore pid key) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [Peers.peerCreateCore_run] at run
  cases run
  cases device : w.dev with
  | none =>
    funext other
    simpa [Peers.creationCoreWorld,txQueueContents,handoffTxView,device] using congrFun before other
  | some d =>
    funext other
    by_cases same : pid = other
    · subst other
      simp [Peers.creationCoreWorld,txQueueContents,handoffTxView,device,Peers.createdPeer,PrevQueue.all,empty]
    · simpa [Peers.creationCoreWorld,txQueueContents,handoffTxView,device,Std.TreeMap.getElem?_insert,same]
        using congrFun before other

private theorem read_bounded (initial : PeerId → List (List SkbId)) (f : Device → WG.M α)
    (next : ∀d, initial d.nextPeer = [] → Preserves (fun w => txQueueContents w = initial) (f d)) :
    Hoare (getDev >>= f) (fun w => PeerSlotsBounded w ∧ txQueueContents w = initial)
      (fun _ w => txQueueContents w = initial) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨d,u,c,read,tail⟩ := run
  cases device : w.dev with
  | none => simp [getDev,device,invariant,AmbientM.invariant] at read; cases read
  | some dev =>
    simp [getDev,device] at read
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := read
    have empty : dev.peers[dev.nextPeer]? = none := by
      cases found : dev.peers[dev.nextPeer]? with
      | none => rfl
      | some p => exact False.elim ((Nat.lt_irrefl _) (before.1 dev device _ p found))
    have point : initial dev.nextPeer = [] := by
      rw [←before.2]
      simp [txQueueContents,handoffTxView,device,empty]
    exact (hoare_iff_run_ambient _ _ _).mp (next dev point) w a result v b before.2 tail

theorem wire (key : Key) (psk : Option Key) : SameView txCryptWire (peerCreate key psk) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  rw [←Peers.peerCreateFactored_eq]
  unfold Peers.peerCreateFactored
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc]
  repeat' first
    | (rx_retention_head Peers.peerCreateCore; exact (core_wire _ _).wp (· = initial))
    | (rx_retention_head dstCacheReset
       exact ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.dstCacheReset_cryptWire) _).wp (· = initial))
    | (rx_retention_head handshakeInit; exact (handshake_init_wire _ _).wp (· = initial))
    | (rx_retention_head resetLastSentHandshake; exact (reset_wire _).wp (· = initial))
    | occurrence_handshake_wire initial

theorem contents (key : Key) (psk : Option Key) (initial : PeerId → List (List SkbId)) :
    Hoare (peerCreate key psk) (fun w => PeerSlotsBounded w ∧ txQueueContents w = initial)
      (fun _ w => txQueueContents w = initial) := by
  rw [←Peers.peerCreateFactored_eq]
  unfold Peers.peerCreateFactored
  apply read_bounded initial
  intro d fresh
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc]
  repeat' first
    | (rx_retention_head Peers.peerCreateCore; exact core_contents initial _ _ fresh)
    | (rx_retention_head dstCacheReset
       exact (contents_factor (ownership_queues ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OwnershipSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.dstCacheReset_ownership) _))).wp (· = initial))
    | (rx_retention_head handshakeInit; exact (handshake_init_contents _ _).wp (· = initial))
    | (rx_retention_head resetLastSentHandshake; exact (reset_contents _).wp (· = initial))
    | occurrence_handshake_contents initial

theorem create (key : Key) (psk : Option Key) : Preserves (Ready locals active) (peerCreate key psk) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp (wire key psk) w a result v b run
  have owners := (hoare_iff_run_ambient _ _ _).mp (contents key psk (txQueueContents w))
    w a result v b ⟨before.1.choose_spec.peerSlots,rfl⟩ run
  exact ⟨Allocated.native (peerCreateMixed_erases key psk) (peerCreateMixed_preserves key psk)
      before.1 a b run,
    before.2.1.queueContents owners (congrArg Prod.snd fields),
    before.2.2.frame_packets (congrArg Prod.fst fields)
      (fun _ owned => owned.queueContents owners) (congrArg Prod.snd fields)⟩

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceCreation
