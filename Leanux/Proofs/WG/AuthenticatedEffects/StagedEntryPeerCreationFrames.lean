import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueueGeometry
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryControlFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySavedFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrencePeerCreation

/-! Creation preserves old packet obligations at the native fresh peer slot.
The slot bound is explicit here and must come from the initialized lifetime
carrier; no arbitrary overwrite is treated as an empty-peer frame. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.PeerCreationFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity Queues.RxCredits
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

theorem handshake_init (pid : PeerId) (psk : Option Key) :
    SameView StagedEntry.view (handshakeInit pid psk) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold handshakeInit IndexOwner.setPeerWord
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head precomputeStaticStatic; exact (SavedFrames.precompute _).wp (· = initial))
    | entry_key_maintenance initial

theorem core_queues (initial : Nat → PeerId → Nat → List WG.Packet) (pid : PeerId) (key : Key)
    (empty : ∀ epoch stamp, initial epoch pid stamp = []) :
    Preserves (fun w => QueueGeometry.queues w = initial) (Peers.peerCreateCore pid key) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [Peers.peerCreateCore_run] at run
  cases run
  funext epoch other stamp
  have original := congrFun (congrFun (congrFun before epoch) other) stamp
  cases device : w.dev with
  | none => simpa [QueueGeometry.queues,stagedPackets,Packets.epoch,Staged.stagedAt,
      Peers.creationCoreWorld,device] using original
  | some d =>
    by_cases same : pid = other
    · subst other
      simp [QueueGeometry.queues,stagedPackets,Packets.epoch,Staged.stagedAt,
        Peers.creationCoreWorld,device,Peers.createdPeer,empty]
    · simpa [QueueGeometry.queues,stagedPackets,Packets.epoch,Staged.stagedAt,
        Peers.creationCoreWorld,device,Std.TreeMap.getElem?_insert,same] using original

theorem read_bounded (initial : Nat → PeerId → Nat → List WG.Packet) (f : Device → WG.M α)
    (next : ∀ d, (∀ epoch stamp, initial epoch d.nextPeer stamp = []) →
      Preserves (fun w => QueueGeometry.queues w = initial) (f d)) :
    Hoare (getDev >>= f) (fun w => PeerSlotsBounded w ∧ QueueGeometry.queues w = initial)
      (fun _ w => QueueGeometry.queues w = initial) := by
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
    have point : ∀ epoch stamp, initial epoch dev.nextPeer stamp = [] := by
      intro epoch stamp
      rw [← before.2]
      simp [QueueGeometry.queues,stagedPackets,Packets.epoch,Staged.stagedAt,device,empty]
    exact (hoare_iff_run_ambient _ _ _).mp (next dev point) w a result v b before.2 tail

theorem queues (key : Key) (psk : Option Key) (initial : Nat → PeerId → Nat → List WG.Packet) :
    Hoare (peerCreate key psk) (fun w => PeerSlotsBounded w ∧ QueueGeometry.queues w = initial)
      (fun _ w => QueueGeometry.queues w = initial) := by
  rw [← Peers.peerCreateFactored_eq]
  unfold Peers.peerCreateFactored
  apply read_bounded initial
  intro d fresh
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc]
  repeat' first
    | (rx_retention_head Peers.peerCreateCore; exact core_queues initial _ _ fresh)
    | (rx_retention_head dstCacheReset; exact (QueueGeometry.of_view (EndpointFrames.reset _)).wp (· = initial))
    | (rx_retention_head handshakeInit; exact (QueueGeometry.of_view (handshake_init _ _)).wp (· = initial))
    | (rx_retention_head resetLastSentHandshake; exact (QueueGeometry.of_view (ControlFrames.reset_handshake _)).wp (· = initial))
    | (rx_retention_head modifyDev
       apply (QueueGeometry.of_view ?_).wp (· = initial)
       apply ReceiveFrames.device <;> intro e <;> rfl)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem geometry (key : Key) (psk : Option Key) :
    SameView StagingOccurrences.geometry (peerCreate key psk) := by
  intro initial
  change Preserves (fun w => StagingOccurrences.geometry w = initial) _
  unfold peerCreate
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc]
  repeat' first
    | (rx_retention_head dstCacheReset; exact (AllocatedObligation.CompletionGeometry.cache_reset _).wp (· = initial))
    | (rx_retention_head handshakeInit
       exact ((handshake_init _ _).of_factor (fun s => (s.2.2.2.1,s.2.2.2.2.1))
         StagingOccurrences.geometry (fun _ => rfl)).wp (· = initial))
    | (rx_retention_head resetLastSentHandshake
       exact ((ControlFrames.reset_handshake _).of_factor (fun s => (s.2.2.2.1,s.2.2.2.2.1))
         StagingOccurrences.geometry (fun _ => rfl)).wp (· = initial))
    | (rx_retention_head invariant; unfold invariant; exact hoare_liftAmbient _ _)
    | staging_geometry_step initial

theorem create (key : Key) (psk : Option Key) :
    Hoare (peerCreate key psk)
      (fun w => Inv history ledger debts locals w ∧ PeerSlotsBounded w)
      (fun _ w => Inv history ledger debts locals w ∧ PeerSlotsBounded w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have wire := (ProjectedAction.iff_run_ambient _ _ _).mp (OccurrenceCreation.wire key psk) w a result v b run
  have epoch := congrArg (Option.map Prod.fst) (congrArg Prod.fst wire)
  have staged := (hoare_iff_run_ambient _ _ _).mp (queues key psk (QueueGeometry.queues w))
    w a result v b ⟨before.2,rfl⟩ run
  have store := (ProjectedAction.iff_run_ambient _ _ _).mp (geometry key psk) w a result v b run
  have owners := (hoare_iff_run_ambient _ _ _).mp (OccurrenceCreation.contents key psk (txQueueContents w))
    w a result v b ⟨before.2,rfl⟩ run
  refine ⟨QueueGeometry.transport before.1 ?_ staged (congrArg Prod.snd store)
    (congrArg Prod.fst store) owners,peerCreate_peerSlots key psk w v result a b before.2 run⟩
  simpa only [txCryptWire,TxRing.nativeCell,Packets.epoch,Option.map_map,Function.comp_def] using epoch

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.PeerCreationFrames
