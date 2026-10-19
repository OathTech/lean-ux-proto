import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialActorFrames
import Leanux.Proofs.WG.AuthenticatedEffects.TransportFrontFrames

/-! Native transmit routing and staging splices preserve the receive key
allocation carrier, including failed route lookup and stopped source guards. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AuthenticatedEffects Responder Origins.Retaining Std.Do
set_option maxHeartbeats 600000

theorem bounded_modify_device (f : Device → Device)
    (epoch : ∀ d, (f d).ifindex = d.ifindex) (packets : ∀ d, (f d).rxSkbs = d.rxSkbs)
    (keys : ∀ d, (f d).keypairs = d.keypairs)
    (frontier : ∀ d, (f d).nextKeypairId = d.nextKeypairId) :
    Preserves (Bounded h) (modifyDev f) := by
  apply bounded_frame (TransportCarrier.modifyDev_rx f epoch packets)
  · exact ResidentMaterial.core_of_same
      (pool_of_material (modifyDev_material f (fun d => Prod.ext (epoch d) (keys d))))
  · intro bound
    apply ResidentMaterial.lower_frame
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    cases run
    simp only [ResidentMaterial.cursor,Option.map_map,Function.comp_def,frontier]

theorem bounded_lookup (family addr : Nat) : Preserves (Bounded h) (lookupDst family addr) := by
  apply bounded_frame (TransportHookFrames.lookup family addr)
    (ResidentMaterial.core_of_same (pool_of_material (lookupDst_material family addr)))
  intro bound
  apply ResidentMaterial.lower_frame
  exact ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotStack.«0».Leanux.Proofs.WG.CurrentSlots.lookupDst_view)
    family addr).of_factor (fun s => s.map Affiliation.State.nextKey) ResidentMaterial.cursor
      (fun _ => by simp only [ResidentMaterial.cursor,Affiliation.view,Option.map_map,Function.comp_def,Affiliation.state])

macro "receive_bounded_native_step" : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer; exact bounded_read_peer _)
  | (rx_retention_head getDev; exact bounded_store getDev_sameWGStore)
  | (rx_retention_head setPeer; exact bounded_set_peer _ _)
  | (rx_retention_head peerPut; exact bounded_peer_put _)
  | (rx_retention_head keypairPut; exact bounded_key_put _ _)
  | (rx_retention_head modifyDev
     exact bounded_modify_device _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Bounded _)
     intro x b
     change Preserves (Bounded _) _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | rx_retention_step)

theorem bounded_trim (pid : PeerId) : Preserves (Bounded h) (xmitTrim pid) := by
  unfold xmitTrim
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
  repeat' receive_bounded_native_step

theorem bounded_splice (pid : PeerId) (packets : List Packet) :
    Preserves (Bounded h) (xmitSplice pid packets) := by
  unfold xmitSplice
  repeat' receive_bounded_native_step

theorem bounded_front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Preserves (Bounded h) (Packets.txFront family addr packets mtu) := by
  have getter (pid : PeerId) : Preserves (Bounded h) (getPeer pid) := bounded_read_peer _
  have pay := bounded_peer_put (h := h)
  have look := bounded_lookup (h := h) family addr
  have trimming := bounded_trim (h := h)
  have splicing := bounded_splice (h := h)
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves (Bounded h) (loopbackSend sites raised) :=
    bounded_store (loopbackSend_kernel sites raised)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Bounded h) (monadLift a : WG.M α) :=
    hoare_liftAmbient a (Bounded h)
  have routing {α : Type} (a : Net.M α) : Preserves (Bounded h) (monadLift a : WG.M α) :=
    bounded_store (liftRouting_sameWGStore a)
  have errors : Preserves (Bounded h) (modifyDev fun d => {d with txErrors := d.txErrors + 1}) :=
    bounded_modify_device _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves (Bounded h) (f x b)) : Preserves (Bounded h) (forIn xs init f) :=
    list_view_spec id (Bounded h) xs init f hf
  rxstack_preserves_source [Packets.txFront,Packets.txCheck,Packets.txSelect,Packets.txError,
      Packets.txHeaders,Packets.txWalk,WG.andM,branch,invariant,skipCutSites,envOk]
    using [getter,look,trimming,splicing,pay,loopback,ambient,routing,errors,loop]

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
