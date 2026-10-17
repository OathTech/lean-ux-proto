import Leanux.Proofs.WG.Queues.BaseCoherenceConfiguration
import Leanux.Proofs.WG.Origins.CurrentRx

/-! Exact structural frames for native RX admission and decryption. The view
contains the live-base list and public-key rows, not peer residency. Normal
reference release may delete peers while these two fields remain unchanged.
No coherence, funding, affiliation, or totality premise is required. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem store_view {α : Type} {action : WG.M α} (same : SameWGStore action) :
    SameView view action :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_store) same

/-- Canonical component transport: the native skb store does not contain either
structural field. Its actual guard and allocation outcomes remain unchanged. -/
theorem skb_view (action : SkbM α) : SameView view (liftSkb action) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceConfiguration.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.skb_frame) action

macro "base_rx_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head liftIndex
     exact ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_index) _).wp (fun s => s = $initial))
  | (rx_retention_head getRxSkb; unfold getRxSkb)
  | (rx_retention_head setRxSkb; unfold setRxSkb)
  | (rx_retention_head newRxSkb; unfold newRxSkb)
  | (rx_retention_head freeRxSkb; unfold freeRxSkb)
  | (rx_retention_head liftSkb; exact (skb_view _).wp (fun s => s = $initial))
  | base_traffic_step $initial)

theorem acquireOwner_view (owner : IndexOwner) : SameView view (Affiliation.acquireOwner owner) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold Affiliation.acquireOwner peerGetMaybeZero IndexOwner.setPeerWord
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,refcountIncNotZero,
    branch,branchCmp,invariant,unsupported]
  repeat' first
    | (rx_retention_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ _)
    | base_rx_step initial

theorem indexLookup_view (kinds : List IndexKind) (index : Nat) :
    SameView view (indexLookup kinds index) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  rw [← Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head Affiliation.acquireOwner; exact (acquireOwner_view _).wp (fun s => s = initial))
    | base_rx_step initial
  exact ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_index) (indexBucket index)).wp (fun s => s = initial)

theorem enqueueDeviceRx_view (id : SkbId) : SameView view (enqueuePerDeviceAndPeerRx id) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold enqueuePerDeviceAndPeerRx
  simp (config := {zeta := false}) only [branch,queueDeviceWork]
  repeat' first
    | (rx_retention_head cpumaskNextOnlineFrom; exact (store_view (cpumaskNextOnlineFrom_sameStore _)).wp (fun s => s = initial))
    | base_rx_step initial

theorem enqueuePeerRx_view (irqExit : WG.M Unit) (irq : SameView view irqExit)
    (id : SkbId) (state : PacketState) : SameView view (enqueuePerPeerRx irqExit id state) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold enqueuePerPeerRx
  simp (config := {zeta := false}) only [invariant,monadLift_self]
  repeat' base_rx_step initial
  all_goals exact irq.wp (fun s => s = initial)

theorem consumeData_view (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    SameView view (consumeData msg src ds) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold consumeData WG.orM keypairGetNull
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact (indexLookup_view _ _).wp (fun s => s = initial))
    | (rx_retention_head enqueuePerDeviceAndPeerRx; exact (enqueueDeviceRx_view _).wp (fun s => s = initial))
    | (rx_retention_head enqueuePerPeerRx; exact (enqueuePeerRx_view _ (SameView.pure _ _) _ _).wp (fun s => s = initial))
    | base_rx_step initial

private theorem cpu_view : SameView view cpumaskNextOnline := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold cpumaskNextOnline
  simp (config := {zeta := false}) only [branch]
  repeat' base_rx_step initial

theorem packetReceive_view (msg : List UInt8) (src : SkbSource) :
    SameView view (packetReceive msg src) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold packetReceive
  simp (config := {zeta := false}) only [branch,unsupported,invariant,queueDeviceWork]
  repeat' first
    | (rx_retention_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp (fun w => view w = initial))
    | (rx_retention_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp (fun w => view w = initial))
    | (rx_retention_head cpumaskNextOnline; exact cpu_view.wp (fun s => s = initial))
    | (rx_retention_head consumeData; exact (consumeData_view _ _ _).wp (fun s => s = initial))
    | base_rx_step initial

theorem wgReceive_view (msg : List UInt8) (src : SkbSource) :
    SameView view (wgReceive msg src) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold wgReceive
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (rx_retention_head packetReceive; exact (packetReceive_view _ _).wp (fun s => s = initial))
    | base_rx_step initial

theorem decryptPacket_view (pkt : RxPacket) : SameView view (decryptPacket pkt) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold decryptPacket WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc,invariant]
  repeat' base_rx_step initial

theorem readDecrypt_view (id : SkbId) : SameView view (RxOrigin.readDecrypt id) := by
  unfold RxOrigin.readDecrypt getRxSkb
  exact (skb_view _).bind (fun pkt => (decryptPacket_view pkt).bind (fun _ => SameView.pure _ _))

theorem counterValidate_view (kid : KeypairId) (nonce : Nat) :
    SameView view (counterValidate kid nonce) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold counterValidate WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,
    Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' base_rx_step initial

/-- The IRQ continuation remains an arbitrary product action; its exact view
contract is the only callback requirement. -/
theorem enqueuePeerRx_product (irqExit : Leanux.M Unit)
    (irq : SameView (fun w : World => view w.wg) irqExit)
    (id : SkbId) (state : PacketState) :
    SameView (fun w : World => view w.wg) (enqueuePerPeerRx irqExit id state) := by
  intro initial
  change Preserves (fun w : World => view w.wg = initial) _
  unfold enqueuePerPeerRx
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (allocation_release_lift_from WG.M
       apply PublicationPoll.native_product (fun g => view g = initial)
       simp only [monadLift_self]
       repeat' base_rx_step initial)
    | (allocation_release_lift_from AmbientM
       exact productAmbient_spec _ _ (fun _ _ h => h))
    | rx_retention_step
  all_goals exact irq.wp (fun s => s = initial)

theorem decryptStep_view (softirq irqExit : Leanux.M Unit)
    (soft : SameView (fun w : World => view w.wg) softirq)
    (irq : SameView (fun w : World => view w.wg) irqExit) :
    SameView (fun w : World => view w.wg) (decryptStep softirq irqExit) := by
  intro initial
  change Preserves (fun w : World => view w.wg = initial) _
  unfold decryptStep
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerPeerRx
       exact (enqueuePeerRx_product irqExit irq _ _).wp (fun s => s = initial))
    | (allocation_release_lift_from WG.M
       apply PublicationPoll.native_product (fun g => view g = initial)
       simp only [monadLift_self]
       repeat' first
         | (rx_retention_head decryptPacket; exact (decryptPacket_view _).wp (fun s => s = initial))
         | base_rx_step initial)
    | (allocation_release_lift_from AmbientM
       exact productAmbient_spec _ _ (fun _ _ h => h))
    | rx_retention_step
  all_goals exact soft.wp (fun s => s = initial)

/-- Any exact structural frame transports coherence without assuming residency
of the listed peers or successful completion of the action. -/
theorem preserves_of_structure {α : Type} {action : WG.M α}
    (same : SameView view action) : Preserves Inv action :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.preserves_of_view) same

end Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
