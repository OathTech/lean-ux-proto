import Leanux.Proofs.WG.RetirementSecurity.OccurrencePeerCreation
import Leanux.Proofs.Framing.WGSocketLifecycle
import Leanux.Proofs.WG.Queues.SlotConfiguration

/-! Actual allowed-IP and socket configuration leaves retain physical TX
ownership; their routing and socket changes are projected away explicitly. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceConfiguration
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits OccurrenceStack OccurrenceHandshake

private theorem aip_wire (action : AipM α) : SameView txCryptWire (liftAip action) := by
  intro initial
  apply hoare_liftAip
  intro w d table before device
  simpa only [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,device,Option.map_some,Option.bind_some] using before

private theorem aip_contents (action : AipM α) : SameView txQueueContents (liftAip action) := by
  intro initial
  apply hoare_liftAip
  intro w d table before device
  funext pid
  simpa only [txQueueContents,handoffTxView,device,Option.bind_some] using congrFun before pid

theorem list_add_wire (pid : PeerId) (node : NodeId) : SameView txCryptWire (listAddTail pid node) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold listAddTail
  repeat' occurrence_handshake_wire initial

theorem list_add_contents (pid : PeerId) (node : NodeId) : SameView txQueueContents (listAddTail pid node) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold listAddTail
  repeat' occurrence_handshake_contents initial

macro "occurrence_aip_wire " initial:term : tactic => `(tactic| first
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (allocation_release_lift_from AipM; exact (aip_wire _).wp (· = $initial))
  | (rx_retention_head liftAip; exact (aip_wire _).wp (· = $initial))
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | occurrence_handshake_wire $initial)

macro "occurrence_aip_contents " initial:term : tactic => `(tactic| first
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (allocation_release_lift_from AipM; exact (aip_contents _).wp (· = $initial))
  | (rx_retention_head liftAip; exact (aip_contents _).wp (· = $initial))
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | occurrence_handshake_contents $initial)

theorem allowedip_add_wire (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView txCryptWire (add root bits key cidr peer) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head listAddTail; exact (list_add_wire _ _).wp (· = initial))
    | (rx_retention_head listDel; exact (OccurrenceAllowedIps.list_delete_wire _).wp (· = initial))
    | occurrence_aip_wire initial

theorem allowedip_add_contents (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView txQueueContents (add root bits key cidr peer) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head listAddTail; exact (list_add_contents _ _).wp (· = initial))
    | (rx_retention_head listDel; exact (OccurrenceAllowedIps.list_delete_contents _).wp (· = initial))
    | occurrence_aip_contents initial

theorem allowedip_insert_wire (family addr cidr : Nat) (pid : PeerId) :
    SameView txCryptWire (WG.insert family addr cidr pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact (allowedip_add_wire _ _ _ _ _).wp (· = initial))
    | occurrence_aip_wire initial

theorem allowedip_insert_contents (family addr cidr : Nat) (pid : PeerId) :
    SameView txQueueContents (WG.insert family addr cidr pid) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact (allowedip_add_contents _ _ _ _ _).wp (· = initial))
    | occurrence_aip_contents initial

theorem allowedip_set_wire (pid : PeerId) (ip : AllowedIpAttrs) : SameView txCryptWire (setAllowedip pid ip) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact (allowedip_insert_wire _ _ _ _).wp (· = initial))
    | occurrence_aip_wire initial

theorem allowedip_set_contents (pid : PeerId) (ip : AllowedIpAttrs) : SameView txQueueContents (setAllowedip pid ip) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact (allowedip_insert_contents _ _ _ _).wp (· = initial))
    | occurrence_aip_contents initial

theorem allowedip_set (pid : PeerId) (ip : AllowedIpAttrs) : Preserves (Ready locals active) (setAllowedip pid ip) :=
  RxPollOccurrences.join (ConfigurationCall.erases (.allowedIp pid ip))
    (ConfigurationCall.allocation (.allowedIp pid ip))
    (occurrences_queueContents (allowedip_set_wire pid ip) (allowedip_set_contents pid ip))

theorem socket_wire {action : WG.M α} (same : SameSocket action) : SameView txCryptWire action :=
  same.of_factor (fun s : WGOwnedView => txCryptWire {dev := s.dev}) _
    (fun w => by simp only [socketView,socketDevice,txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,
      wgOwnedView,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])

theorem socket_contents {action : WG.M α} (same : SameSocket action) : SameView txQueueContents action :=
  same.of_factor (fun s : WGOwnedView => txQueueContents {dev := s.dev}) _
    (fun w => by funext pid; simp only [socketView,socketDevice,txQueueContents,handoffTxView,
      wgOwnedView,wgStoreView,Option.bind_map,Function.comp_def])

theorem socket_init (port : Nat) : Preserves (Ready locals active) (socketInit port) :=
  RxPollOccurrences.join (DeviceControlCall.erases (.init port)) (DeviceControlCall.allocation (.init port))
    (occurrences_queueContents (socket_wire (socketInit_sameSocket port)) (socket_contents (socketInit_sameSocket port)))

theorem socket_reinit (new4 new6 : Option Nat) : Preserves (Ready locals active) (socketReinit new4 new6) :=
  RxPollOccurrences.join (DeviceControlCall.erases (.reinit new4 new6)) (DeviceControlCall.allocation (.reinit new4 new6))
    (occurrences_queueContents (socket_wire (socketReinit_sameSocket new4 new6)) (socket_contents (socketReinit_sameSocket new4 new6)))

theorem set_port_wire (port : Nat) : SameView txCryptWire (setPort port) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact (OccurrenceTimers.clear_endpoint_wire _).wp (· = initial))
    | (rx_retention_head socketInit; exact (socket_wire (socketInit_sameSocket _)).wp (· = initial))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => txCryptWire w = initial)
       intro x b
       change Preserves (fun w => txCryptWire w = initial) _)
    | occurrence_handshake_wire initial

theorem set_port (port : Nat) : Preserves (Ready locals active) (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact OccurrenceTimers.clear_endpoint _)
    | (rx_retention_head socketInit; exact socket_init _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Ready locals active)
       intro x b
       change Preserves (Ready locals active) _)
    | occurrence_ready_step

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceConfiguration
