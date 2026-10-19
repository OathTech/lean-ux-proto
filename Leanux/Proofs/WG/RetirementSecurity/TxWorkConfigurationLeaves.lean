import Leanux.Proofs.WG.RetirementSecurity.TxWorkLifecycle

/-! Original configuration leaves retain TX service. Fresh peer creation
uses the actual allocation frontier to retain existing queue contents; the
new empty peer is not assumed to occupy a vacant arbitrary numeric slot. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem precompute_work (pid : PeerId) : SameView queued (precomputeStaticStatic pid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold precomputeStaticStatic requireNotPending
  simp (config := {zeta := false}) only [branch]
  repeat' handshake_work_step initial

theorem handshake_init_work (pid : PeerId) (psk : Option Key) : SameView queued (handshakeInit pid psk) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold handshakeInit IndexOwner.setPeerWord
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head precomputeStaticStatic; exact (precompute_work _).wp (·=initial))
    | handshake_work_step initial

theorem peer_create_core_work (pid : PeerId) (key : Key) : SameView queued (Peers.peerCreateCore pid key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  rw [Peers.peerCreateCore_run] at run
  cases run
  simp only [Peers.creationCoreWorld,queued,Option.map_map,Function.comp_def]

theorem peer_create_work (key : Key) (psk : Option Key) : SameView queued (peerCreate key psk) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  rw [←Peers.peerCreateFactored_eq]
  unfold Peers.peerCreateFactored
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc]
  repeat' first
    | (rx_retention_head Peers.peerCreateCore; exact (peer_create_core_work _ _).wp (·=initial))
    | (rx_retention_head dstCacheReset
       exact ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxWorkSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.TxWork.dstCacheReset_work) _).wp (·=initial))
    | (rx_retention_head handshakeInit; exact (handshake_init_work _ _).wp (·=initial))
    | (rx_retention_head resetLastSentHandshake; exact (reset_work _).wp (·=initial))
    | handshake_work_step initial

theorem serving_peer_create (key : Key) (psk : Option Key) :
    Preserves (Serving locals crypt tx) (peerCreate key psk) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have wire:=(ProjectedAction.iff_run_ambient _ _ _).mp (OccurrenceCreation.wire key psk) w a result v b run
  have queues:=(hoare_iff_run_ambient _ _ _).mp (OccurrenceCreation.contents key psk (txQueueContents w))
    w a result v b ⟨before.2.1.1.choose_spec.peerSlots,rfl⟩ run
  exact ⟨before.1.contents queues (congrArg Prod.snd wire) (crypt_items_eq (congrArg Prod.fst wire))
    ((ProjectedAction.iff_run_ambient _ _ _).mp (peer_create_work key psk) w a result v b run),
    (hoare_iff_run_ambient _ _ _).mp (TxCovered.Configuration.create key psk) w a result v b before.2 run⟩

theorem serving_pubkey (key : Key) : Preserves (Serving locals crypt tx) (pubkeyLookup key) :=
  serving_join (passive_contents (OccurrenceHandshake.pubkey_lookup_wire key)
    (OccurrenceHandshake.pubkey_lookup_contents key) (pubkey_lookup_work key)) (TxCovered.Configuration.pubkey key)

theorem serving_precompute (pid : PeerId) : Preserves (Serving locals crypt tx) (precomputeStaticStatic pid) :=
  serving_join (passive_contents (OccurrenceCreation.precompute_wire pid)
    (OccurrenceCreation.precompute_contents pid) (precompute_work pid)) (TxCovered.Configuration.precompute pid)

theorem aip_list_add_work (pid : PeerId) (node : NodeId) : SameView queued (listAddTail pid node) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold listAddTail
  repeat' handshake_work_step initial

macro "aip_work_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (allocation_release_lift_from AipM; exact (aip_work _).wp (·=$initial))
  | (rx_retention_head liftAip; exact (aip_work _).wp (·=$initial))
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | handshake_work_step $initial)

theorem aip_add_work (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView queued (add root bits key cidr peer) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head listAddTail; exact (aip_list_add_work _ _).wp (·=initial))
    | (rx_retention_head listDel; exact (aip_list_delete_work _).wp (·=initial))
    | aip_work_step initial

theorem aip_insert_work (family addr cidr : Nat) (pid : PeerId) :
    SameView queued (WG.insert family addr cidr pid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact (aip_add_work _ _ _ _ _).wp (·=initial))
    | aip_work_step initial

theorem aip_set_work (pid : PeerId) (ip : AllowedIpAttrs) : SameView queued (setAllowedip pid ip) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact (aip_insert_work _ _ _ _).wp (·=initial))
    | aip_work_step initial

theorem serving_aip_set (pid : PeerId) (ip : AllowedIpAttrs) :
    Preserves (Serving locals crypt tx) (setAllowedip pid ip) :=
  serving_join (passive_contents (OccurrenceConfiguration.allowedip_set_wire pid ip)
    (OccurrenceConfiguration.allowedip_set_contents pid ip) (aip_set_work pid ip))
    (TxCovered.Configuration.allowedip_set pid ip)

theorem serving_set_port (port : Nat) : Preserves (Serving locals crypt tx) (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact serving_clear_endpoint _)
    | (rx_retention_head socketInit; exact serving_socket_init _)
    | serving_removal_step

end Leanux.Proofs.WG.RetirementSecurity.TxWork
